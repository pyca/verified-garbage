// The functions of `src/rsa.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute:
	str x0, [x4, #128]
	str x2, [x4, #136]
	str x3, [x4, #144]
	add x0, x4, #0
	ldrb w5, [x2, #0]
	sub x6, x3, #1
	add x6, x2, x6
	ldrb w6, [x6, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x10, x5, x8
	csel x10, x8, x7, hs
	and x6, x6, x8
	sub x11, x3, #64
	lsl x11, x11, #8
	add x11, x11, x5
	movz x12, #128, lsl #0
	subs x12, x11, x12
	csel x11, x8, x7, hs
	and x9, x10, x6
	and x9, x9, x11
	cbz x9, 20f
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
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
	ldr x1, [x0, #136]
	ldr x8, [x0, #64]
	ldr x2, [x0, #144]
	movz x6, #7, lsl #0
	and x4, x2, x6
	cbz x4, 22f
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
24:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 25f
	b 26f
25:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
26:
	cbnz x2, 24b
	b 23f
22:
	add x5, x8, x2
27:
	ldr x3, [x1, #0]
	rev x3, x3
	sub x5, x5, #8
	str x3, [x5, #0]
	add x1, x1, #8
	sub x2, x2, #8
	cbnz x2, 27b
23:
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
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 28f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
210:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 210b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
211:
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
	cbnz x13, 211b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
212:
	ldr x8, [x0, #80]
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
	add x16, x8, #0
	add x14, x12, #2
213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 213b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
214:
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
	cbnz x14, 214b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
215:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 215b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 216f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
218:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 217f
216:
217:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 219f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
221:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 221b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 220f
219:
220:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 222b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 212b
	b 29f
28:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 223f
225:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 225b
	b 224f
223:
224:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
226:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 226b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
227:
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
228:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 228b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 229b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
230:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 227b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
231:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 231b
29:
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	ldr x17, [x0, #128]
	add x14, x12, #0
232:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 232b
	ldr x16, [x0, #96]
	add x14, x12, #0
233:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 233b
	movz x0, #1, lsl #0
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	add x2, x2, #7
	lsr x2, x2, #3
	lsl x2, x2, #1
	movz x3, #0, lsl #0
234:
	str x3, [x1, #0]
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 234b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_rsa_public_precomputed_checked:
	movz x16, #65535, lsl #0
	movk x16, #65535, lsl #16
	movk x16, #3, lsl #32
	movz x17, #0, lsl #0
	movz x15, #1, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
20:
	lsl x10, x10, #8
	add x12, x4, x11
	ldrb w12, [x12, #0]
	add x10, x10, x12
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x10, x10, x16, eq
	add x11, x11, #1
	sub x14, x5, x11
	cbnz x14, 20b
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x13, x15, x17, eq
	and x14, x10, x15
	movz x12, #3, lsl #0
	subs x12, x10, x12
	csel x12, x15, x17, hs
	and x9, x13, x14
	and x9, x9, x12
	cbz x9, 21f
	ldr x8, [sp, #0]
	str x0, [x8, #128]
	str x2, [x8, #136]
	str x1, [x8, #144]
	str x4, [x8, #152]
	str x5, [x8, #160]
	str x6, [x8, #168]
	add x0, x8, #0
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
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
	ldr x16, [x0, #136]
	ldr x17, [x0, #64]
	add x14, x12, #0
23:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 23b
	ldr x17, [x0, #96]
	add x14, x12, #0
24:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 24b
	ldr x16, [x0, #96]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
25:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 25b
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x17, [x0, #64]
	ldr x3, [x17, #0]
	and x3, x3, x8
	and x9, x9, x3
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x17, x4
	ldr x3, [x4, #0]
	subs x3, x3, x8
	csel x3, x8, x7, hs
	and x9, x9, x3
	cbz x9, 26f
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	ldr x8, [x0, #72]
	movz x6, #7, lsl #0
	and x4, x2, x6
	cbz x4, 28f
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
210:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 211f
	b 212f
211:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
212:
	cbnz x2, 210b
	b 29f
28:
	add x5, x8, x2
213:
	ldr x3, [x1, #0]
	rev x3, x3
	sub x5, x5, #8
	str x3, [x5, #0]
	add x1, x1, #8
	sub x2, x2, #8
	cbnz x2, 213b
29:
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 214b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #176]
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
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
215:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 216f
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
218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 218b
	add x13, x12, #0
219:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
220:
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
	cbnz x14, 220b
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
221:
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
	cbnz x14, 221b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 219b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
222:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 222b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
223:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 223b
	b 217f
216:
	cbz x4, 224f
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
226:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 226b
	add x13, x12, #0
227:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
228:
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
	cbnz x14, 228b
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
229:
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
	cbnz x14, 229b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 227b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
230:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
231:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 231b
	b 225f
224:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
232:
	str x7, [x16, #0]
	str x7, [x16, #8]
	str x7, [x16, #16]
	str x7, [x16, #24]
	str x7, [x16, #32]
	str x7, [x16, #40]
	str x7, [x16, #48]
	str x7, [x16, #56]
	add x16, x16, #64
	sub x14, x14, #1
	cbnz x14, 232b
	str x7, [x16, #0]
	str x7, [x16, #8]
	mov v16.d[0], x19
	mov v17.d[0], x20
	mov v18.d[0], x21
	mov v19.d[0], x22
	mov v20.d[0], x23
	mov v21.d[0], x24
	mov v22.d[0], x25
	mov v23.d[0], x26
	mov v24.d[0], x27
	mov v25.d[0], x28
	mov v26.d[0], x30
	ldr x8, [x0, #72]
	lsr x12, x12, #3
233:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #96]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
234:
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adds x1, x7, x7
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 234b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 233b
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	ldr x16, [x0, #104]
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	str x27, [x16, #64]
	str x28, [x16, #72]
	str x30, [x16, #80]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
235:
	ldr x19, [x8, #0]
	ldr x20, [x8, #8]
	ldr x21, [x8, #16]
	ldr x22, [x8, #24]
	ldr x23, [x8, #32]
	ldr x24, [x8, #40]
	ldr x25, [x8, #48]
	ldr x26, [x8, #56]
	ldr x17, [x0, #64]
	ldr x15, [x0, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	mul x27, x19, x15
	str x27, [x8, #0]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #8]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #16]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #24]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #32]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #40]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #48]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #56]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x16, x8, #64
	add x17, x17, #64
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, #1
236:
	ldr x13, [x16, #0]
	adds x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 236b
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 235b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #104]
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x27, [x16, #64]
	ldr x28, [x16, #72]
	ldr x30, [x16, #80]
	ldr x5, [x0, #104]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
237:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	sbcs x3, x3, x4
	str x3, [x13, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	sbcs x3, x3, x4
	str x3, [x13, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	sbcs x3, x3, x4
	str x3, [x13, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x13, x13, #32
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
238:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x6, #8]
	csel x3, x4, x3, hs
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x6, #16]
	csel x3, x4, x3, hs
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x6, #24]
	csel x3, x4, x3, hs
	str x3, [x5, #24]
	add x16, x16, #32
	add x6, x6, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 238b
225:
217:
	ldr x3, [x0, #160]
	sub x3, x3, #3
	cbz x3, 239f
	movz x3, #0, lsl #0
	str x3, [x0, #184]
	str x3, [x0, #216]
241:
	ldr x3, [x0, #152]
	ldr x4, [x0, #184]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #200]
	movz x3, #8, lsl #0
	str x3, [x0, #192]
242:
	ldr x3, [x0, #216]
	cbnz x3, 243f
	b 244f
243:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
244:
	ldr x3, [x0, #200]
	lsr x3, x3, #7
	movz x4, #1, lsl #0
	and x3, x3, x4
	cbnz x3, 245f
	b 246f
245:
	ldr x3, [x0, #216]
	cbnz x3, 247f
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	add x14, x12, #0
249:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 249b
	movz x3, #1, lsl #0
	str x3, [x0, #216]
	b 248f
247:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 250f
	ldr x8, [x0, #80]
	ldr x9, [x0, #104]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
252:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 252b
	add x13, x12, #0
253:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
254:
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
	cbnz x14, 254b
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
255:
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
	cbnz x14, 255b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 253b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
256:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
257:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 257b
	b 251f
250:
	cbz x4, 258f
	ldr x8, [x0, #80]
	ldr x9, [x0, #104]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
260:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 260b
	add x13, x12, #0
261:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
262:
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
	cbnz x14, 262b
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
263:
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
	cbnz x14, 263b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 261b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
264:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
265:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 265b
	b 259f
258:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
266:
	str x7, [x16, #0]
	str x7, [x16, #8]
	str x7, [x16, #16]
	str x7, [x16, #24]
	str x7, [x16, #32]
	str x7, [x16, #40]
	str x7, [x16, #48]
	str x7, [x16, #56]
	add x16, x16, #64
	sub x14, x14, #1
	cbnz x14, 266b
	str x7, [x16, #0]
	str x7, [x16, #8]
	mov v16.d[0], x19
	mov v17.d[0], x20
	mov v18.d[0], x21
	mov v19.d[0], x22
	mov v20.d[0], x23
	mov v21.d[0], x24
	mov v22.d[0], x25
	mov v23.d[0], x26
	mov v24.d[0], x27
	mov v25.d[0], x28
	mov v26.d[0], x30
	ldr x8, [x0, #112]
	lsr x12, x12, #3
267:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
268:
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adds x1, x7, x7
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 268b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 267b
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	ldr x16, [x0, #112]
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	str x27, [x16, #64]
	str x28, [x16, #72]
	str x30, [x16, #80]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
269:
	ldr x19, [x8, #0]
	ldr x20, [x8, #8]
	ldr x21, [x8, #16]
	ldr x22, [x8, #24]
	ldr x23, [x8, #32]
	ldr x24, [x8, #40]
	ldr x25, [x8, #48]
	ldr x26, [x8, #56]
	ldr x17, [x0, #64]
	ldr x15, [x0, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	mul x27, x19, x15
	str x27, [x8, #0]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #8]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #16]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #24]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #32]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #40]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #48]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #56]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x16, x8, #64
	add x17, x17, #64
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, #1
270:
	ldr x13, [x16, #0]
	adds x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 270b
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 269b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #112]
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x27, [x16, #64]
	ldr x28, [x16, #72]
	ldr x30, [x16, #80]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	sbcs x3, x3, x4
	str x3, [x13, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	sbcs x3, x3, x4
	str x3, [x13, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	sbcs x3, x3, x4
	str x3, [x13, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x13, x13, #32
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
272:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x6, #8]
	csel x3, x4, x3, hs
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x6, #16]
	csel x3, x4, x3, hs
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x6, #24]
	csel x3, x4, x3, hs
	str x3, [x5, #24]
	add x16, x16, #32
	add x6, x6, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 272b
259:
251:
248:
246:
	ldr x3, [x0, #200]
	add x3, x3, x3
	str x3, [x0, #200]
	ldr x3, [x0, #192]
	sub x3, x3, #1
	str x3, [x0, #192]
	cbnz x3, 242b
	ldr x3, [x0, #184]
	add x3, x3, #1
	str x3, [x0, #184]
	ldr x4, [x0, #160]
	sub x3, x4, x3
	cbnz x3, 241b
	b 240f
239:
	ldr x8, [x0, #152]
	ldrb w3, [x8, #0]
	sub x3, x3, #1
	ldrb w4, [x8, #1]
	orr x3, x3, x4
	ldrb w4, [x8, #2]
	sub x4, x4, #1
	orr x3, x3, x4
	cbz x3, 273f
	movz x3, #0, lsl #0
	str x3, [x0, #184]
	str x3, [x0, #216]
275:
	ldr x3, [x0, #152]
	ldr x4, [x0, #184]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #200]
	movz x3, #8, lsl #0
	str x3, [x0, #192]
276:
	ldr x3, [x0, #216]
	cbnz x3, 277f
	b 278f
277:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
278:
	ldr x3, [x0, #200]
	lsr x3, x3, #7
	movz x4, #1, lsl #0
	and x3, x3, x4
	cbnz x3, 279f
	b 280f
279:
	ldr x3, [x0, #216]
	cbnz x3, 281f
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	add x14, x12, #0
283:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
	movz x3, #1, lsl #0
	str x3, [x0, #216]
	b 282f
281:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 284f
	ldr x8, [x0, #80]
	ldr x9, [x0, #104]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
286:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 286b
	add x13, x12, #0
287:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
288:
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
	cbnz x14, 288b
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
289:
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
	cbnz x14, 289b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 287b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
290:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
291:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 291b
	b 285f
284:
	cbz x4, 292f
	ldr x8, [x0, #80]
	ldr x9, [x0, #104]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
294:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 294b
	add x13, x12, #0
295:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
296:
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
	cbnz x14, 296b
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
297:
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
	cbnz x14, 297b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 295b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
298:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 298b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
299:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 299b
	b 293f
292:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
2100:
	str x7, [x16, #0]
	str x7, [x16, #8]
	str x7, [x16, #16]
	str x7, [x16, #24]
	str x7, [x16, #32]
	str x7, [x16, #40]
	str x7, [x16, #48]
	str x7, [x16, #56]
	add x16, x16, #64
	sub x14, x14, #1
	cbnz x14, 2100b
	str x7, [x16, #0]
	str x7, [x16, #8]
	mov v16.d[0], x19
	mov v17.d[0], x20
	mov v18.d[0], x21
	mov v19.d[0], x22
	mov v20.d[0], x23
	mov v21.d[0], x24
	mov v22.d[0], x25
	mov v23.d[0], x26
	mov v24.d[0], x27
	mov v25.d[0], x28
	mov v26.d[0], x30
	ldr x8, [x0, #112]
	lsr x12, x12, #3
2101:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
2102:
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adds x1, x7, x7
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2102b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2101b
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	ldr x16, [x0, #112]
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	str x27, [x16, #64]
	str x28, [x16, #72]
	str x30, [x16, #80]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
2103:
	ldr x19, [x8, #0]
	ldr x20, [x8, #8]
	ldr x21, [x8, #16]
	ldr x22, [x8, #24]
	ldr x23, [x8, #32]
	ldr x24, [x8, #40]
	ldr x25, [x8, #48]
	ldr x26, [x8, #56]
	ldr x17, [x0, #64]
	ldr x15, [x0, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	mul x27, x19, x15
	str x27, [x8, #0]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #8]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #16]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #24]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #32]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #40]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #48]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #56]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x16, x8, #64
	add x17, x17, #64
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, #1
2104:
	ldr x13, [x16, #0]
	adds x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2104b
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2103b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #112]
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x27, [x16, #64]
	ldr x28, [x16, #72]
	ldr x30, [x16, #80]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
2105:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	sbcs x3, x3, x4
	str x3, [x13, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	sbcs x3, x3, x4
	str x3, [x13, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	sbcs x3, x3, x4
	str x3, [x13, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x13, x13, #32
	sub x14, x14, #1
	cbnz x14, 2105b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2106:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x6, #8]
	csel x3, x4, x3, hs
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x6, #16]
	csel x3, x4, x3, hs
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x6, #24]
	csel x3, x4, x3, hs
	str x3, [x5, #24]
	add x16, x16, #32
	add x6, x6, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 2106b
293:
285:
282:
280:
	ldr x3, [x0, #200]
	add x3, x3, x3
	str x3, [x0, #200]
	ldr x3, [x0, #192]
	sub x3, x3, #1
	str x3, [x0, #192]
	cbnz x3, 276b
	ldr x3, [x0, #184]
	add x3, x3, #1
	str x3, [x0, #184]
	ldr x4, [x0, #160]
	sub x3, x4, x3
	cbnz x3, 275b
	b 274f
273:
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	add x14, x12, #0
2107:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	movz x3, #1, lsl #0
	str x3, [x0, #216]
	movz x3, #16, lsl #0
	str x3, [x0, #184]
2108:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #184]
	sub x3, x3, #1
	str x3, [x0, #184]
	cbnz x3, 2108b
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2109f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2111:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	add x13, x12, #0
2112:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2113:
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
	cbnz x14, 2113b
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
2114:
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
	cbnz x14, 2114b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2112b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2115:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2116:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	b 2110f
2109:
	cbz x4, 2117f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2119:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	add x13, x12, #0
2120:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2121:
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
	cbnz x14, 2121b
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
2122:
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
	cbnz x14, 2122b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2120b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2123:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2123b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2124:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	b 2118f
2117:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
2125:
	str x7, [x16, #0]
	str x7, [x16, #8]
	str x7, [x16, #16]
	str x7, [x16, #24]
	str x7, [x16, #32]
	str x7, [x16, #40]
	str x7, [x16, #48]
	str x7, [x16, #56]
	add x16, x16, #64
	sub x14, x14, #1
	cbnz x14, 2125b
	str x7, [x16, #0]
	str x7, [x16, #8]
	mov v16.d[0], x19
	mov v17.d[0], x20
	mov v18.d[0], x21
	mov v19.d[0], x22
	mov v20.d[0], x23
	mov v21.d[0], x24
	mov v22.d[0], x25
	mov v23.d[0], x26
	mov v24.d[0], x27
	mov v25.d[0], x28
	mov v26.d[0], x30
	ldr x8, [x0, #72]
	lsr x12, x12, #3
2126:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #112]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
2127:
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adds x1, x7, x7
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2127b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2126b
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	ldr x16, [x0, #112]
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	str x27, [x16, #64]
	str x28, [x16, #72]
	str x30, [x16, #80]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
2128:
	ldr x19, [x8, #0]
	ldr x20, [x8, #8]
	ldr x21, [x8, #16]
	ldr x22, [x8, #24]
	ldr x23, [x8, #32]
	ldr x24, [x8, #40]
	ldr x25, [x8, #48]
	ldr x26, [x8, #56]
	ldr x17, [x0, #64]
	ldr x15, [x0, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	mul x27, x19, x15
	str x27, [x8, #0]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #8]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #16]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #24]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #32]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #40]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #48]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #56]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x16, x8, #64
	add x17, x17, #64
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, #1
2129:
	ldr x13, [x16, #0]
	adds x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2129b
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2128b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #112]
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x27, [x16, #64]
	ldr x28, [x16, #72]
	ldr x30, [x16, #80]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
2130:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	sbcs x3, x3, x4
	str x3, [x13, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	sbcs x3, x3, x4
	str x3, [x13, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	sbcs x3, x3, x4
	str x3, [x13, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x13, x13, #32
	sub x14, x14, #1
	cbnz x14, 2130b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2131:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x6, #8]
	csel x3, x4, x3, hs
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x6, #16]
	csel x3, x4, x3, hs
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x6, #24]
	csel x3, x4, x3, hs
	str x3, [x5, #24]
	add x16, x16, #32
	add x6, x6, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 2131b
2118:
2110:
	movz x3, #2, lsl #0
	str x3, [x0, #216]
274:
240:
	ldr x3, [x0, #216]
	sub x3, x3, #2
	cbz x3, 2132f
	ldr x3, [x0, #216]
	cbnz x3, 2134f
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	b 2135f
2134:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2137f
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2139:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2139b
	add x13, x12, #0
2140:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2141:
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
	cbnz x14, 2141b
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
2142:
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
	cbnz x14, 2142b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2140b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2143:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2144:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	b 2138f
2137:
	cbz x4, 2145f
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2147:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	add x13, x12, #0
2148:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2149:
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
	cbnz x14, 2149b
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
2150:
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
	cbnz x14, 2150b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2148b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2151:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2152:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	b 2146f
2145:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
2153:
	str x7, [x16, #0]
	str x7, [x16, #8]
	str x7, [x16, #16]
	str x7, [x16, #24]
	str x7, [x16, #32]
	str x7, [x16, #40]
	str x7, [x16, #48]
	str x7, [x16, #56]
	add x16, x16, #64
	sub x14, x14, #1
	cbnz x14, 2153b
	str x7, [x16, #0]
	str x7, [x16, #8]
	mov v16.d[0], x19
	mov v17.d[0], x20
	mov v18.d[0], x21
	mov v19.d[0], x22
	mov v20.d[0], x23
	mov v21.d[0], x24
	mov v22.d[0], x25
	mov v23.d[0], x26
	mov v24.d[0], x27
	mov v25.d[0], x28
	mov v26.d[0], x30
	ldr x8, [x0, #112]
	lsr x12, x12, #3
2154:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
2155:
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adds x1, x7, x7
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2155b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2154b
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	ldr x16, [x0, #112]
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	str x27, [x16, #64]
	str x28, [x16, #72]
	str x30, [x16, #80]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
2156:
	ldr x19, [x8, #0]
	ldr x20, [x8, #8]
	ldr x21, [x8, #16]
	ldr x22, [x8, #24]
	ldr x23, [x8, #32]
	ldr x24, [x8, #40]
	ldr x25, [x8, #48]
	ldr x26, [x8, #56]
	ldr x17, [x0, #64]
	ldr x15, [x0, #56]
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	mul x27, x19, x15
	str x27, [x8, #0]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #8]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #16]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #24]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #32]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #40]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #48]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	mul x27, x19, x15
	str x27, [x8, #56]
	movz x1, #0, lsl #0
	movz x13, #1, lsl #0
	subs x13, x19, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x16, x8, #64
	add x17, x17, #64
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, #1
2157:
	ldr x13, [x16, #0]
	adds x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	ldr x2, [x17, #8]
	ldr x3, [x17, #16]
	ldr x4, [x17, #24]
	ldr x5, [x17, #32]
	ldr x6, [x17, #40]
	ldr x9, [x17, #48]
	ldr x11, [x17, #56]
	adc x1, x7, x7
	ldr x27, [x8, #0]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #8]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #16]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #24]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #32]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #40]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #48]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	adc x1, x7, x7
	ldr x27, [x8, #56]
	ldr x13, [x17, #0]
	mul x13, x27, x13
	mul x14, x27, x2
	mul x28, x27, x3
	mul x30, x27, x4
	adds x19, x19, x13
	mul x13, x27, x5
	adcs x20, x20, x14
	mul x14, x27, x6
	adcs x21, x21, x28
	mul x28, x27, x9
	adcs x22, x22, x30
	mul x30, x27, x11
	adcs x23, x23, x13
	ldr x13, [x17, #0]
	umulh x13, x27, x13
	adcs x24, x24, x14
	umulh x14, x27, x2
	adcs x25, x25, x28
	umulh x28, x27, x3
	adcs x26, x26, x30
	umulh x30, x27, x4
	adc x1, x1, x7
	str x19, [x16, #0]
	add x16, x16, #8
	adds x19, x20, x13
	umulh x13, x27, x5
	adcs x20, x21, x14
	umulh x14, x27, x6
	adcs x21, x22, x28
	umulh x28, x27, x9
	adcs x22, x23, x30
	umulh x30, x27, x11
	adcs x23, x24, x13
	adcs x24, x25, x14
	adcs x25, x26, x28
	adcs x26, x1, x30
	add x17, x17, #64
	sub x15, x15, #1
	cbnz x15, 2157b
	movz x1, #1, lsl #0
	subs x1, x10, x1
	ldr x13, [x16, #0]
	adcs x19, x19, x13
	ldr x13, [x16, #8]
	adcs x20, x20, x13
	ldr x13, [x16, #16]
	adcs x21, x21, x13
	ldr x13, [x16, #24]
	adcs x22, x22, x13
	ldr x13, [x16, #32]
	adcs x23, x23, x13
	ldr x13, [x16, #40]
	adcs x24, x24, x13
	ldr x13, [x16, #48]
	adcs x25, x25, x13
	ldr x13, [x16, #56]
	adcs x26, x26, x13
	adc x10, x7, x7
	str x19, [x16, #0]
	str x20, [x16, #8]
	str x21, [x16, #16]
	str x22, [x16, #24]
	str x23, [x16, #32]
	str x24, [x16, #40]
	str x25, [x16, #48]
	str x26, [x16, #56]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2156b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #112]
	ldr x19, [x16, #0]
	ldr x20, [x16, #8]
	ldr x21, [x16, #16]
	ldr x22, [x16, #24]
	ldr x23, [x16, #32]
	ldr x24, [x16, #40]
	ldr x25, [x16, #48]
	ldr x26, [x16, #56]
	ldr x27, [x16, #64]
	ldr x28, [x16, #72]
	ldr x30, [x16, #80]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
2158:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	sbcs x3, x3, x4
	str x3, [x13, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	sbcs x3, x3, x4
	str x3, [x13, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	sbcs x3, x3, x4
	str x3, [x13, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x13, x13, #32
	sub x14, x14, #1
	cbnz x14, 2158b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2159:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x6, #8]
	csel x3, x4, x3, hs
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x6, #16]
	csel x3, x4, x3, hs
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x6, #24]
	csel x3, x4, x3, hs
	str x3, [x5, #24]
	add x16, x16, #32
	add x6, x6, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 2159b
2146:
2138:
2135:
	b 2133f
2132:
2133:
	ldr x8, [x0, #112]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x6, #7, lsl #0
	and x2, x9, x6
	cbz x2, 2160f
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2162:
	and x5, x2, x6
	cbz x5, 2163f
	b 2164f
2163:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2164:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2162b
	b 2161f
2160:
	add x5, x8, #0
2165:
	ldr x3, [x5, #0]
	and x3, x3, x15
	rev x3, x3
	sub x1, x1, #8
	str x3, [x1, #0]
	add x5, x5, #8
	sub x9, x9, #8
	cbnz x9, 2165b
2161:
	ldr x0, [x0, #176]
	movz x3, #1, lsl #0
	and x0, x0, x3
	b 27f
26:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2166:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2166b
	movz x0, #0, lsl #0
27:
	b 22f
21:
	add x10, x0, #0
	add x11, x1, #0
	movz x12, #0, lsl #0
2167:
	strb w12, [x10, #0]
	add x10, x10, #1
	sub x11, x11, #1
	cbnz x11, 2167b
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6

vg_rsa_crt_values:
	ldr x8, [sp, #48]
	str x0, [x8, #128]
	str x1, [x8, #168]
	str x2, [x8, #152]
	str x3, [x8, #184]
	str x4, [x8, #160]
	str x6, [x8, #136]
	str x7, [x8, #144]
	ldr x9, [sp, #0]
	str x9, [x8, #192]
	ldr x9, [sp, #16]
	str x9, [x8, #200]
	ldr x9, [sp, #32]
	str x9, [x8, #208]
	ldr x9, [sp, #40]
	str x9, [x8, #216]
	add x0, x8, #0
	add x2, x6, #0
	add x3, x7, #0
	ldrb w5, [x2, #0]
	sub x6, x3, #1
	add x6, x2, x6
	ldrb w6, [x6, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x10, x5, x8
	csel x10, x8, x7, hs
	and x6, x6, x8
	sub x11, x3, #64
	lsl x11, x11, #8
	add x11, x11, x5
	movz x12, #128, lsl #0
	subs x12, x11, x12
	csel x11, x8, x7, hs
	and x9, x10, x6
	and x9, x9, x11
	cbz x9, 20f
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
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
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
23:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 24f
	b 25f
24:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
25:
	cbnz x2, 23b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
27:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 28f
	b 29f
28:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
29:
	cbnz x2, 27b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
211:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 212f
	b 213f
212:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
213:
	cbnz x2, 211b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #208]
	ldr x2, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
215:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 216f
	b 217f
216:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
217:
	cbnz x2, 215b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
219:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
220:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 220b
	lsl x6, x12, #6
221:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
222:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
223:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
224:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 224b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
225:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
226:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 226b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
227:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 227b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 228b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	movz x7, #0, lsl #0
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
229:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
230:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
232:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 232b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
233:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 233b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
234:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsl x6, x12, #7
235:
	movz x7, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	add x9, x15, #0
	subs x3, x7, x7
236:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 236b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	and x15, x15, x9
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
237:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x5, x3, x4
	and x5, x5, x15
	eor x3, x3, x5
	eor x4, x4, x5
	str x3, [x16, #0]
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
238:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x5, x3, x4
	and x5, x5, x15
	eor x3, x3, x5
	eor x4, x4, x5
	str x3, [x16, #0]
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	movz x7, #0, lsl #0
	add x15, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
239:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 239b
	add x15, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
240:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 240b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
241:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 241b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
242:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 242b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
243:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 243b
	adc x3, x7, x7
	str x3, [x5, #0]
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
244:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 244b
	sub x6, x6, #1
	cbnz x6, 235b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
246:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 246b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
247:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
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
248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 248b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
250:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 250b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
251:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 251b
	lsl x6, x12, #6
252:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
253:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 253b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
254:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 254b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
255:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 255b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
256:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 256b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 252b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
257:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
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
258:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
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
260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
261:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
262:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 262b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
263:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
	lsl x6, x12, #6
264:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
265:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
266:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
267:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 268b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #168]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
269:
	and x5, x2, x6
	cbz x5, 270f
	b 271f
270:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
271:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 269b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x9, [x0, #168]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
272:
	and x5, x2, x6
	cbz x5, 273f
	b 274f
273:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
274:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #152]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
275:
	and x5, x2, x6
	cbz x5, 276f
	b 277f
276:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
277:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 275b
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
278:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 278b
	ldr x1, [x0, #152]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
279:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 279b
	ldr x1, [x0, #160]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
280:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 280b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_rsa_recover_primes:
	ldr x8, [sp, #16]
	str x0, [x8, #128]
	str x2, [x8, #168]
	str x4, [x8, #136]
	str x5, [x8, #144]
	str x6, [x8, #152]
	str x7, [x8, #160]
	ldr x9, [sp, #0]
	str x9, [x8, #184]
	ldr x9, [sp, #8]
	str x9, [x8, #192]
	add x0, x8, #0
	add x2, x4, #0
	add x3, x5, #0
	ldrb w5, [x2, #0]
	sub x6, x3, #1
	add x6, x2, x6
	ldrb w6, [x6, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x10, x5, x8
	csel x10, x8, x7, hs
	and x6, x6, x8
	sub x11, x3, #64
	lsl x11, x11, #8
	add x11, x11, x5
	movz x12, #128, lsl #0
	subs x12, x11, x12
	csel x11, x8, x7, hs
	and x9, x10, x6
	and x9, x9, x11
	cbz x9, 20f
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
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
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
23:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 24f
	b 25f
24:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
25:
	cbnz x2, 23b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #152]
	ldr x2, [x0, #160]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
27:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 28f
	b 29f
28:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
29:
	cbnz x2, 27b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
211:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 212f
	b 213f
212:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
213:
	cbnz x2, 211b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x3, [x16, #0]
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
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
215:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x11, x5, #0
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x13, x3, #3
	movz x7, #0, lsl #0
216:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
217:
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
	cbnz x14, 217b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 216b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x5, x3, x4
	sub x3, x3, x5
	str x3, [x16, #0]
	sub x5, x5, #1
	str x5, [x0, #240]
	movz x9, #0, lsl #0
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
218:
	ldr x3, [x16, #0]
	orr x9, x9, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 218b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #240]
	orr x10, x15, x3
	cbz x10, 219f
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
221:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 221b
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
222:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 222b
	movz x0, #0, lsl #0
	b 220f
219:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	lsl x6, x14, #6
	movz x3, #0, lsl #0
	str x3, [x0, #216]
223:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
224:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
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
	ldr x3, [x17, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
	ldr x3, [x0, #216]
	sub x3, x3, x15
	str x3, [x0, #216]
225:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	sub x6, x6, #1
	cbnz x6, 223b
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 226f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
228:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 228b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
229:
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
	cbnz x13, 229b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
230:
	ldr x8, [x0, #80]
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
	add x16, x8, #0
	add x14, x12, #2
231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 231b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
232:
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
	cbnz x14, 232b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
233:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 233b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
234:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
235:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 235b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
236:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 230b
	b 227f
226:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 237f
239:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 239b
	b 238f
237:
238:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
241:
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
242:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 242b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
243:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 243b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
244:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 241b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
245:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 245b
227:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
246:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 246b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
247:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
248:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 248b
	movz x3, #0, lsl #0
	str x3, [x0, #200]
249:
	ldr x9, [x0, #200]
	add x9, x9, #2
	movz x13, #0, lsl #0
	ldr x12, [x0, #48]
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
250:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 250b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_4}
	umov x30, v31.d[0]
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
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
251:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 251b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
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
252:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	ldr x3, [x0, #200]
	cbz x3, 253f
	ldr x3, [x0, #200]
	sub x3, x3, #1
	cbz x3, 255f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	str x14, [x0, #232]
257:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #232]
	sub x3, x3, #1
	lsl x3, x3, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	str x3, [x0, #240]
	movz x3, #64, lsl #0
	str x3, [x0, #248]
258:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
259:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x3, [x0, #240]
	lsr x4, x3, #63
	add x3, x3, x3
	str x3, [x0, #240]
	movz x7, #0, lsl #0
	sub x15, x7, x4
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
260:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	sub x3, x3, #1
	str x3, [x0, #248]
	cbnz x3, 258b
	ldr x3, [x0, #232]
	sub x3, x3, #1
	str x3, [x0, #232]
	cbnz x3, 257b
	b 256f
255:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	str x14, [x0, #232]
261:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #232]
	sub x3, x3, #1
	lsl x3, x3, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	str x3, [x0, #240]
	movz x3, #64, lsl #0
	str x3, [x0, #248]
262:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x9, [x0, #112]
	ldr x17, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
263:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
264:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
265:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x9, [x0, #104]
	ldr x17, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
266:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
267:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
268:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x3, [x0, #240]
	lsr x4, x3, #63
	add x3, x3, x3
	str x3, [x0, #240]
	movz x7, #0, lsl #0
	sub x15, x7, x4
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
269:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x3, [x0, #248]
	sub x3, x3, #1
	str x3, [x0, #248]
	cbnz x3, 262b
	ldr x3, [x0, #232]
	sub x3, x3, #1
	str x3, [x0, #232]
	cbnz x3, 261b
256:
	b 254f
253:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	str x14, [x0, #232]
270:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #232]
	sub x3, x3, #1
	lsl x3, x3, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	str x3, [x0, #240]
	movz x3, #64, lsl #0
	str x3, [x0, #248]
271:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x9, [x0, #112]
	ldr x17, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
272:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
273:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 273b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
274:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 274b
	ldr x3, [x0, #240]
	lsr x4, x3, #63
	add x3, x3, x3
	str x3, [x0, #240]
	movz x7, #0, lsl #0
	sub x15, x7, x4
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
275:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 275b
	ldr x3, [x0, #248]
	sub x3, x3, #1
	str x3, [x0, #248]
	cbnz x3, 271b
	ldr x3, [x0, #232]
	sub x3, x3, #1
	str x3, [x0, #232]
	cbnz x3, 270b
254:
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
276:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #240]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
277:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 277b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #240]
	orr x15, x15, x3
	str x15, [x0, #240]
	str x7, [x0, #248]
	str x7, [x0, #232]
278:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
279:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
280:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 280b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #176]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
281:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 281b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x10, x15, #0
	ldr x3, [x0, #232]
	ldr x4, [x0, #216]
	subs x3, x3, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x5, x15, #0
	ldr x3, [x0, #232]
	add x3, x3, #1
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	orr x10, x10, x15
	sub x4, x7, #1
	ldr x3, [x0, #240]
	eor x3, x3, x4
	and x5, x5, x3
	ldr x2, [x0, #176]
	and x13, x5, x2
	orr x3, x2, x10
	and x3, x3, x5
	ldr x1, [x0, #240]
	orr x3, x3, x1
	str x3, [x0, #240]
	ldr x3, [x0, #248]
	orr x3, x3, x13
	str x3, [x0, #248]
	eor x5, x5, x4
	orr x3, x2, x10
	orr x15, x5, x3
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
282:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 282b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x3, [x0, #160]
	add x3, x3, #7
	lsr x3, x3, #3
	add x14, x3, x12
	lsl x4, x14, #6
	ldr x3, [x0, #232]
	add x3, x3, #1
	str x3, [x0, #232]
	sub x3, x4, x3
	cbnz x3, 278b
	ldr x3, [x0, #200]
	add x3, x3, #1
	str x3, [x0, #200]
	movz x4, #100, lsl #0
	movz x7, #0, lsl #0
	subs x3, x3, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #248]
	eor x3, x3, x4
	and x15, x15, x3
	cbnz x15, 249b
	ldr x3, [x0, #248]
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_7}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
284:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 284b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
285:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 285b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
286:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 286b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
288:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 288b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsl x6, x12, #7
289:
	movz x7, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
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
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	add x9, x15, #0
	subs x3, x7, x7
290:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 290b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	and x15, x15, x9
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
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
291:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x5, x3, x4
	and x5, x5, x15
	eor x3, x3, x5
	eor x4, x4, x5
	str x3, [x16, #0]
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 291b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
292:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x5, x3, x4
	and x5, x5, x15
	eor x3, x3, x5
	eor x4, x4, x5
	str x3, [x16, #0]
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	movz x7, #0, lsl #0
	add x15, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
293:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 293b
	add x15, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
294:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 294b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x0, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
295:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 295b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
296:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 296b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x0, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
297:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 297b
	adc x3, x7, x7
	str x3, [x5, #0]
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
298:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
	sub x6, x6, #1
	cbnz x6, 289b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
299:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2101:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	lsl x6, x12, #6
2102:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2103:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2104:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
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
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
2105:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2106:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2102b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2107:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2108:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x5, x3, x4
	and x5, x5, x15
	eor x3, x3, x5
	eor x4, x4, x5
	str x3, [x16, #0]
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2109:
	and x5, x2, x6
	cbz x5, 2110f
	b 2111f
2110:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2111:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2109b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2112:
	and x5, x2, x6
	cbz x5, 2113f
	b 2114f
2113:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2114:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2112b
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
220:
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2115:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2115b
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2116:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2116b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_rsa_check_key:
	ldr x8, [sp, #64]
	str x0, [x8, #136]
	str x1, [x8, #144]
	str x2, [x8, #152]
	str x3, [x8, #160]
	str x4, [x8, #128]
	str x5, [x8, #168]
	str x6, [x8, #184]
	str x7, [x8, #192]
	ldr x9, [sp, #0]
	str x9, [x8, #200]
	ldr x9, [sp, #8]
	str x9, [x8, #208]
	ldr x9, [sp, #16]
	str x9, [x8, #216]
	ldr x9, [sp, #32]
	str x9, [x8, #232]
	ldr x9, [sp, #48]
	str x9, [x8, #240]
	add x0, x8, #0
	add x4, x2, #0
	add x5, x3, #0
	movz x16, #65535, lsl #0
	movk x16, #65535, lsl #16
	movk x16, #3, lsl #32
	movz x17, #0, lsl #0
	movz x15, #1, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
20:
	lsl x10, x10, #8
	add x12, x4, x11
	ldrb w12, [x12, #0]
	add x10, x10, x12
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x10, x10, x16, eq
	add x11, x11, #1
	sub x14, x5, x11
	cbnz x14, 20b
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x13, x15, x17, eq
	and x14, x10, x15
	movz x12, #3, lsl #0
	subs x12, x10, x12
	csel x12, x15, x17, hs
	and x9, x13, x14
	and x9, x9, x12
	cbz x9, 21f
	ldr x2, [x0, #136]
	ldr x3, [x0, #144]
	ldrb w5, [x2, #0]
	sub x6, x3, #1
	add x6, x2, x6
	ldrb w6, [x6, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x10, x5, x8
	csel x10, x8, x7, hs
	and x6, x6, x8
	sub x11, x3, #64
	lsl x11, x11, #8
	add x11, x11, x5
	movz x12, #128, lsl #0
	subs x12, x11, x12
	csel x11, x8, x7, hs
	and x9, x10, x6
	and x9, x9, x11
	cbz x9, 23f
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	add x12, x12, x12
	add x12, x12, #2
	str x12, [x0, #48]
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
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
25:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 25b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
26:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 27f
	b 28f
27:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
28:
	cbnz x2, 26b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
29:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 29b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #152]
	ldr x2, [x0, #160]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
210:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 211f
	b 212f
211:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
212:
	cbnz x2, 210b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 213b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
215:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 216f
	b 217f
216:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
217:
	cbnz x2, 215b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
218:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
220:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 221f
	b 222f
221:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
222:
	cbnz x2, 220b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
224:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 225f
	b 226f
225:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
226:
	cbnz x2, 224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
227:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 227b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x5, x11, #0
	add x5, x5, x0
	add x5, x5, #256
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x11, x5, #0
	sub x12, x12, #2
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
228:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
229:
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
	cbnz x14, 229b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 228b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
230:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
232:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 233f
	b 234f
233:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
234:
	cbnz x2, 232b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
235:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #216]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
236:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 237f
	b 238f
237:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
238:
	cbnz x2, 236b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
239:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 239b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
241:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 242f
	b 243f
242:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
243:
	cbnz x2, 241b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
245:
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
	cbnz x14, 245b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
246:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 246b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
247:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 248b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
249:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 249b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	lsl x6, x13, #6
250:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
251:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 251b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
252:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 252b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 253b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
254:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 254b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 250b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
255:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #216]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
257:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 258f
	b 259f
258:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
259:
	cbnz x2, 257b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
260:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
261:
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
	cbnz x14, 261b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
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
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
263:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
264:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
265:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	lsl x6, x13, #6
266:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
267:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
268:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
269:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
270:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 270b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
272:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
273:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 274f
	b 275f
274:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
275:
	cbnz x2, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
276:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 276b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #232]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
277:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 278f
	b 279f
278:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
279:
	cbnz x2, 277b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
280:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 280b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
281:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 281b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
282:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 283f
	b 284f
283:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
284:
	cbnz x2, 282b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
285:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 285b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
286:
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
	cbnz x14, 286b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
288:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 288b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #192]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
289:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 289b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #192]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
290:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #192]
	add x13, x13, #7
	lsr x13, x13, #3
	add x13, x13, #1
	lsl x6, x13, #6
291:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
292:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 292b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
293:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 293b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
294:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 294b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
295:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 295b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 291b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
296:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 296b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
297:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 297b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #232]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
298:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 299f
	b 2100f
299:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2100:
	cbnz x2, 298b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2101:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2102:
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
	cbnz x14, 2102b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2103:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2104:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
2105:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
2106:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	lsl x6, x13, #6
2107:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
2108:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2109:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
2110:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2111:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2107b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
2112:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2113:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2114:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2115f
	b 2116f
2115:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2116:
	cbnz x2, 2114b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2117:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #240]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2118:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2119f
	b 2120f
2119:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2120:
	cbnz x2, 2118b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
2121:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2122:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2123:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2124f
	b 2125f
2124:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2125:
	cbnz x2, 2123b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2126:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2126b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x5, x11, #0
	add x5, x5, x0
	add x5, x5, #256
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x11, x5, #0
	sub x12, x12, #2
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
2127:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2128:
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
	cbnz x14, 2128b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2127b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2129:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2130:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
2131:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2131b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
2132:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	lsl x6, x13, #6
2133:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
2134:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2134b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2135:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
2136:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2137:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2133b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
2138:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
	b 24f
23:
	movz x0, #0, lsl #0
24:
	b 22f
21:
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6

vg_rsa_check_crt_key:
	ldr x8, [sp, #48]
	str x0, [x8, #136]
	str x1, [x8, #144]
	str x2, [x8, #152]
	str x3, [x8, #160]
	str x4, [x8, #128]
	str x5, [x8, #168]
	str x4, [x8, #184]
	str x5, [x8, #192]
	str x6, [x8, #200]
	str x7, [x8, #208]
	ldr x9, [sp, #0]
	str x9, [x8, #216]
	ldr x9, [sp, #16]
	str x9, [x8, #232]
	ldr x9, [sp, #32]
	str x9, [x8, #240]
	add x0, x8, #0
	add x4, x2, #0
	add x5, x3, #0
	movz x16, #65535, lsl #0
	movk x16, #65535, lsl #16
	movk x16, #3, lsl #32
	movz x17, #0, lsl #0
	movz x15, #1, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
20:
	lsl x10, x10, #8
	add x12, x4, x11
	ldrb w12, [x12, #0]
	add x10, x10, x12
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x10, x10, x16, eq
	add x11, x11, #1
	sub x14, x5, x11
	cbnz x14, 20b
	lsr x13, x10, #33
	adds x13, x13, x17
	csel x13, x15, x17, eq
	and x14, x10, x15
	movz x12, #3, lsl #0
	subs x12, x10, x12
	csel x12, x15, x17, hs
	and x9, x13, x14
	and x9, x9, x12
	cbz x9, 21f
	ldr x2, [x0, #136]
	ldr x3, [x0, #144]
	ldrb w5, [x2, #0]
	sub x6, x3, #1
	add x6, x2, x6
	ldrb w6, [x6, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x10, x5, x8
	csel x10, x8, x7, hs
	and x6, x6, x8
	sub x11, x3, #64
	lsl x11, x11, #8
	add x11, x11, x5
	movz x12, #128, lsl #0
	subs x12, x11, x12
	csel x11, x8, x7, hs
	and x9, x10, x6
	and x9, x9, x11
	cbz x9, 23f
	ldr x3, [x0, #144]
	add x12, x3, #15
	lsr x12, x12, #4
	ldr x3, [x0, #192]
	add x3, x3, #7
	lsr x3, x3, #3
	subs x4, x12, x3
	csel x12, x12, x3, hs
	ldr x3, [x0, #208]
	add x3, x3, #7
	lsr x3, x3, #3
	subs x4, x12, x3
	csel x12, x12, x3, hs
	add x12, x12, x12
	add x12, x12, #2
	str x12, [x0, #48]
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
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
25:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 25b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
26:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 27f
	b 28f
27:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
28:
	cbnz x2, 26b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
29:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 29b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #152]
	ldr x2, [x0, #160]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
210:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 211f
	b 212f
211:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
212:
	cbnz x2, 210b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 213b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
215:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 216f
	b 217f
216:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
217:
	cbnz x2, 215b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
219:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 220f
	b 221f
220:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
221:
	cbnz x2, 219b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
222:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x5, x11, #0
	add x5, x5, x0
	add x5, x5, #256
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x11, x5, #0
	sub x12, x12, #2
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
223:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
224:
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
	cbnz x14, 224b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 223b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
225:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
226:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 226b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
227:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 228f
	b 229f
228:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
229:
	cbnz x2, 227b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
230:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #216]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
231:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 232f
	b 233f
232:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
233:
	cbnz x2, 231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
234:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 234b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
235:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
236:
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
	cbnz x14, 236b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
238:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
239:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 239b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
240:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	lsl x6, x13, #6
241:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
242:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 242b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
243:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 243b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
244:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
245:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 245b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 241b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
246:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 246b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
247:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
248:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 249f
	b 250f
249:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
250:
	cbnz x2, 248b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	sub x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
251:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 251b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #232]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
252:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 253f
	b 254f
253:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
254:
	cbnz x2, 252b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
255:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x1, x11, #0
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x1
	add x1, x1, x0
	add x1, x1, #256
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x1, #0]
	sub x12, x12, #2
	lsr x12, x12, #1
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
257:
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
	cbnz x14, 257b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
258:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
261:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 261b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x13, #1, lsl #0
	lsl x6, x13, #6
262:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
263:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
264:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
265:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
266:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 266b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 262b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
267:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
268:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #184]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
269:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 270f
	b 271f
270:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
271:
	cbnz x2, 269b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
272:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #240]
	ldr x2, [x0, #192]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
273:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 274f
	b 275f
274:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
275:
	cbnz x2, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
276:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 277b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x2, [x0, #208]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
278:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 279f
	b 280f
279:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
280:
	cbnz x2, 278b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
281:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 281b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x5, x11, #0
	add x5, x5, x0
	add x5, x5, #256
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x11, x5, #0
	sub x12, x12, #2
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
282:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
283:
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
	cbnz x14, 283b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 282b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
284:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 284b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
285:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 285b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	lsl x3, x13, #3
	add x16, x16, x3
	sub x12, x12, x13
	add x14, x12, #0
286:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 286b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	add x16, x11, #0
	add x16, x16, x16
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
	sub x3, x12, x13
	lsl x3, x3, #3
	add x17, x17, x3
	add x12, x13, #0
	add x14, x12, #0
287:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 287b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x13, [x0, #208]
	add x13, x13, #7
	lsr x13, x13, #3
	lsl x6, x13, #6
288:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
289:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 289b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
290:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 290b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
291:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 291b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
292:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 288b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
293:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 293b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
	b 24f
23:
	movz x0, #0, lsl #0
24:
	b 22f
21:
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6

vg_rsa_private_checked:
	str x30, [sp, #-16]!
	sub sp, sp, #3232
	add x15, sp, #0
	str x0, [x15, #80]
	str x2, [x15, #88]
	str x3, [x15, #96]
	str x4, [x15, #104]
	str x5, [x15, #112]
	str x6, [x15, #120]
	ldr x8, [sp, #3264]
	str x8, [x15, #0]
	ldr x8, [sp, #3272]
	str x8, [x15, #8]
	ldr x8, [sp, #3280]
	str x8, [x15, #16]
	ldr x8, [sp, #3288]
	str x8, [x15, #24]
	ldr x8, [sp, #3296]
	str x8, [x15, #32]
	ldr x8, [sp, #3304]
	str x8, [x15, #40]
	ldr x8, [sp, #3312]
	str x8, [x15, #48]
	ldr x8, [sp, #3320]
	str x8, [x15, #56]
	ldr x8, [sp, #3328]
	str x8, [x15, #64]
	ldr x8, [sp, #3336]
	str x8, [x15, #72]
	add x0, sp, #160
	add x1, x3, #0
	add x4, x6, #0
	add x5, x3, #0
	ldr x6, [sp, #3248]
	ldr x7, [sp, #3256]
	bl {vg_rsa_private_crt}
	add x15, sp, #0
	str x0, [x15, #128]
	add x0, sp, #1184
	ldr x1, [sp, #96]
	add x1, x1, #7
	lsr x1, x1, #3
	add x1, x1, x1
	ldr x2, [sp, #88]
	ldr x3, [sp, #96]
	ldr x4, [sp, #3328]
	ldr x5, [sp, #3336]
	bl {vg_rsa_public_precompute}
	add x15, sp, #0
	str x0, [x15, #136]
	ldr x0, [sp, #80]
	ldr x1, [sp, #96]
	add x2, sp, #1184
	ldr x3, [sp, #96]
	add x3, x3, #7
	lsr x3, x3, #3
	add x3, x3, x3
	ldr x4, [sp, #104]
	ldr x5, [sp, #112]
	add x6, sp, #160
	add x7, x1, #0
	ldr x8, [sp, #3328]
	str x8, [x15, #0]
	ldr x8, [sp, #3336]
	str x8, [x15, #8]
	bl {vg_rsa_public_precomputed_checked}
	ldr x10, [sp, #128]
	and x9, x0, x10
	ldr x10, [sp, #136]
	and x9, x9, x10
	movz x10, #1, lsl #0
	and x9, x9, x10
	ldr x11, [sp, #80]
	ldr x12, [sp, #120]
	ldr x13, [sp, #96]
	movz x14, #0, lsl #0
20:
	ldrb w8, [x11, #0]
	ldrb w10, [x12, #0]
	eor x8, x8, x10
	orr x14, x14, x8
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 20b
	movz x10, #0, lsl #0
	movz x13, #1, lsl #0
	adds x8, x14, x10
	csel x8, x13, x10, eq
	movz x13, #2, lsl #0
	sub x13, x13, x8
	sub x12, x10, x9
	and x13, x13, x12
	and x8, x8, x9
	sub x12, x10, x8
	ldr x11, [sp, #80]
	add x14, sp, #160
	ldr x15, [sp, #96]
21:
	ldrb w8, [x14, #0]
	and x8, x8, x12
	strb w8, [x11, #0]
	strb w10, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x15, x15, #1
	cbnz x15, 21b
	add x0, x13, #0
	add sp, sp, #3232
	ldr x30, [sp], #16
	ret
	.p2align 6
