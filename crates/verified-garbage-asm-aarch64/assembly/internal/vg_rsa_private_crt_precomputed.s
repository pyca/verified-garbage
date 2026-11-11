// The functions of `src/internal/vg_rsa_private_crt_precomputed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_precomputed:
	ldr x8, [sp, #64]
	str x0, [x8, #128]
	str x2, [x8, #136]
	str x3, [x8, #144]
	str x4, [x8, #168]
	str x6, [x8, #152]
	str x7, [x8, #160]
	ldr x9, [sp, #0]
	str x9, [x8, #184]
	ldr x9, [sp, #8]
	str x9, [x8, #192]
	ldr x9, [sp, #16]
	str x9, [x8, #200]
	ldr x9, [sp, #32]
	str x9, [x8, #216]
	ldr x9, [sp, #48]
	str x9, [x8, #224]
	add x0, x8, #0
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
	ldr x9, [x0, #144]
	lsr x9, x9, #7
	ldr x10, [x0, #160]
	ldr x11, [x0, #192]
	orr x10, x10, x11
	movz x11, #63, lsl #0
	tst x10, x11
	movz x11, #0, lsl #0
	csel x9, x9, x11, eq
	cbz x9, 22f
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
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	ldr x8, [x0, #72]
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
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
210:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 210b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #176]
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
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 212f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 214b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
215:
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
	cbnz x13, 215b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
216:
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
217:
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
	cbnz x14, 217b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 218f
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
	b 219f
218:
219:
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 216b
	b 213f
212:
	ldr x12, [x0, #48]
	sub x13, x12, #2
	cbz x13, 221f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #24
	add x13, x9, x13
	ldr x15, [x13, #16]
	ldr x3, [x13, #8]
	ldr x4, [x13, #0]
	movz x10, #1, lsl #0
	movz x13, #63, lsl #0
223:
	add x16, x15, x15
	add x17, x10, x10
	tst x15, x15
	csel x15, x16, x15, pl
	csel x10, x17, x10, pl
	sub x13, x13, #1
	cbnz x13, 223b
	mul x16, x3, x10
	umulh x4, x4, x10
	add x16, x16, x4
	umulh x3, x3, x10
	add x15, x15, x3
	str x10, [x6, #8]
	str x15, [x6, #16]
	str x16, [x6, #24]
	ldr x5, [x6, #16]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
224:
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
	cbnz x13, 224b
	str x10, [x6, #0]
	add x8, x11, #0
	movz x9, #1, lsl #0
	sub x13, x12, #1
	add x16, x8, #0
	add x14, x12, #2
225:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 225b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	add x13, x12, #1
	str x13, [x0, #208]
226:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x2, [x16, #16]
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	ldr x17, [x6, #8]
	ldr x5, [x6, #16]
	mul x2, x2, x17
	umulh x15, x3, x17
	add x2, x2, x15
	mul x3, x3, x17
	umulh x15, x4, x17
	add x3, x3, x15
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
	sub x13, x13, #32
	add x16, x11, x13
	ldr x3, [x16, #16]
	ldr x4, [x16, #8]
	ldr x14, [x16, #0]
	sub x15, x12, #3
	tst x15, x15
	csel x14, x15, x14, eq
	ldr x17, [x6, #8]
	mul x3, x3, x17
	umulh x15, x4, x17
	add x3, x3, x15
	mul x4, x4, x17
	umulh x15, x14, x17
	add x4, x4, x15
	ldr x15, [x6, #24]
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
227:
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
	cbnz x14, 227b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 228f
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
230:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 229f
228:
229:
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 226b
	b 222f
221:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 231f
233:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 233b
	b 232f
231:
232:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
234:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
235:
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
236:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 236b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
237:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
238:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 235b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
239:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 239b
222:
213:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_4}
	umov x30, v31.d[0]
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #160]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x5, #2, lsl #0
	subs x6, x12, x5
	csel x12, x12, x5, hs
	add x1, x0, #0
	add x0, x4, #0
	str x1, [x0, #128]
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
	add x0, x1, #0
	ldr x5, [x0, #232]
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	lsl x6, x6, #5
	add x4, x4, x6
	str x4, [x0, #240]
	ldr x12, [x0, #192]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x5, #2, lsl #0
	subs x6, x12, x5
	csel x12, x12, x5, hs
	add x1, x0, #0
	add x0, x4, #0
	str x1, [x0, #128]
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
	add x0, x1, #0
	ldr x0, [x0, #232]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
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
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
245:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 246f
	b 247f
246:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
247:
	cbnz x2, 245b
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
248:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 248b
	ldr x5, [x0, #128]
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
249:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 250f
	b 251f
250:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
251:
	cbnz x2, 249b
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
252:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x5, [x0, #128]
	ldr x3, [x5, #176]
	and x15, x15, x3
	str x15, [x5, #176]
	ldr x5, [x0, #128]
	ldr x5, [x5, #176]
	str x5, [x0, #192]
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	add x14, x12, #0
253:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 253b
	movz x4, #3, lsl #0
	and x5, x15, x4
	eor x5, x5, x4
	ldr x16, [x0, #64]
	ldr x3, [x16, #0]
	orr x3, x3, x5
	str x3, [x16, #0]
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
254:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 254b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x5, [x0, #128]
	ldr x5, [x5, #176]
	str x5, [x0, #192]
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 255b
	movz x4, #3, lsl #0
	and x5, x15, x4
	eor x5, x5, x4
	ldr x16, [x0, #64]
	ldr x3, [x16, #0]
	orr x3, x3, x5
	str x3, [x16, #0]
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
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x0, [x0, #128]
	ldr x5, [x0, #240]
	ldr x5, [x5, #48]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
257:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 257b
	add x3, x3, x5
	sub x3, x3, x12
	lsl x3, x3, #6
	str x3, [x0, #248]
	ldr x12, [x0, #48]
	ldr x10, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x10, x13
	ldr x4, [x13, #0]
	cbz x4, 258f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 260f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
262:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 262b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 261f
260:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 263f
265:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 265b
	b 264f
263:
264:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
266:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 267f
	b 268f
267:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
269:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	adc x3, x7, x7
	str x3, [x16, #0]
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
268:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 266b
261:
	b 259f
258:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 272f
274:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 274b
	b 273f
272:
273:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
275:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 276f
	b 277f
276:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
278:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 278b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
279:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 279b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
280:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 280b
277:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 275b
259:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
281:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 281b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
282:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
284:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 284b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
285:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 285b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
286:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 286b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
287:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 287b
	ldr x3, [x0, #176]
	cbnz x3, 282b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
288:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 288b
	ldr x0, [x0, #128]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_6}
	umov x30, v31.d[0]
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
289:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 289b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
290:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
291:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 291b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
292:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
293:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 293b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
295:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 295b
	ldr x3, [x0, #176]
	cbnz x3, 290b
	ldr x5, [x0, #128]
	ldr x3, [x5, #216]
	str x3, [x0, #136]
	ldr x3, [x5, #192]
	str x3, [x0, #144]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
	ldr x3, [x0, #120]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #200]
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
296:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 296b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #208]
	add x14, x12, #0
297:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
298:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
299:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #208]
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 299b
	movz x3, #0, lsl #0
	str x3, [x0, #216]
	str x3, [x0, #160]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	movz x4, #5, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x9, x4, x5, hs
	cbnz x9, 2101f
	b 2102f
2101:
2103:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	movz x4, #0, lsl #0
	ldrb w5, [x3, #0]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #1]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #2]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #3]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #4]
	lsl x4, x4, #8
	orr x4, x4, x5
	str x4, [x0, #168]
	ldr x3, [x0, #168]
	lsr x3, x3, #35
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #30
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #25
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #20
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #15
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #10
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #5
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #0
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #152]
	add x3, x3, #5
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	movz x4, #5, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x9, x4, x5, hs
	cbnz x9, 2103b
2102:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2104f
	b 2105f
2104:
2106:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #7
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2107f
	b 2108f
2107:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2108:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #6
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2109f
	b 2110f
2109:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2110:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #5
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2111f
	b 2112f
2111:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2112:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #4
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2113f
	b 2114f
2113:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2114:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #3
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2115f
	b 2116f
2115:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2116:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #2
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2117f
	b 2118f
2117:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2118:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #1
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2119f
	b 2120f
2119:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2120:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #0
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2121f
	b 2122f
2121:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2122:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2106b
2105:
	ldr x3, [x0, #160]
	cbnz x3, 2123f
	b 2124f
2123:
2125:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2125b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2126f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2128:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2129:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 2128b
	b 2127f
2126:
	cbz x4, 2130f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2132:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2133:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2133b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 2132b
	b 2131f
2130:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2134:
	ldr x16, [x0, #104]
	sub x16, x17, x16
	ldr x3, [x0, #200]
	add x16, x16, x3
	movi v23.2d, #0
	movz x14, #32, lsl #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
2135:
	cmeq v20.2d, v23.2d, v22.2d
	ldr q21, [x16, #0]
	bit v16.16b, v21.16b, v20.16b
	ldr q21, [x16, #16]
	bit v17.16b, v21.16b, v20.16b
	ldr q21, [x16, #32]
	bit v18.16b, v21.16b, v20.16b
	ldr q21, [x16, #48]
	bit v19.16b, v21.16b, v20.16b
	add x16, x16, x6
	add v23.2d, v23.2d, v24.2d
	sub x14, x14, #1
	cbnz x14, 2135b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2134b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2131:
2127:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2124:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_7}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x5, [x0, #232]
	ldr x5, [x5, #48]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
2136:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2136b
	add x3, x3, x5
	sub x3, x3, x12
	lsl x3, x3, #6
	str x3, [x0, #248]
	ldr x12, [x0, #48]
	ldr x10, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x10, x13
	ldr x4, [x13, #0]
	cbz x4, 2137f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2139f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2141:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2141b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2140f
2139:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2142f
2144:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2144b
	b 2143f
2142:
2143:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2145:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2146f
	b 2147f
2146:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2148:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2149:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2150:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2150b
2147:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2145b
2140:
	b 2138f
2137:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2151f
2153:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2153b
	b 2152f
2151:
2152:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2154:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2155f
	b 2156f
2155:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2157:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2157b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2158:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2159:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2159b
2156:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2154b
2138:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2160:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2161:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2162:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2163:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2164:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2164b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2165:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2165b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2166:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	ldr x3, [x0, #176]
	cbnz x3, 2161b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2167:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2167b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2168:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2168b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2169:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2169b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_6}
	umov x30, v31.d[0]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2170:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2170b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2171:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2172:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2172b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2173:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2174:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2174b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2175:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2175b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2176:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	ldr x3, [x0, #176]
	cbnz x3, 2171b
	ldr x5, [x0, #128]
	ldr x3, [x5, #200]
	str x3, [x0, #136]
	ldr x3, [x5, #160]
	str x3, [x0, #144]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
	ldr x3, [x0, #120]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #200]
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2177:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2177b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #208]
	add x14, x12, #0
2178:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2178b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2179:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2180:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #208]
	add x14, x12, #0
2181:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2181b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2180b
	movz x3, #0, lsl #0
	str x3, [x0, #216]
	str x3, [x0, #160]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	movz x4, #5, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x9, x4, x5, hs
	cbnz x9, 2182f
	b 2183f
2182:
2184:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	movz x4, #0, lsl #0
	ldrb w5, [x3, #0]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #1]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #2]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #3]
	lsl x4, x4, #8
	orr x4, x4, x5
	ldrb w5, [x3, #4]
	lsl x4, x4, #8
	orr x4, x4, x5
	str x4, [x0, #168]
	ldr x3, [x0, #168]
	lsr x3, x3, #35
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #30
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #25
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #20
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #15
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #10
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #5
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #168]
	lsr x3, x3, #0
	movz x4, #31, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
	ldr x3, [x0, #152]
	add x3, x3, #5
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	movz x4, #5, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x9, x4, x5, hs
	cbnz x9, 2184b
2183:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2185f
	b 2186f
2185:
2187:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #7
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2188f
	b 2189f
2188:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2189:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #6
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2190f
	b 2191f
2190:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2191:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #5
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2192f
	b 2193f
2192:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2193:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #4
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2194f
	b 2195f
2194:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2195:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #3
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2196f
	b 2197f
2196:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2197:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #2
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2198f
	b 2199f
2198:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2199:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #1
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2200f
	b 2201f
2200:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2201:
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	ldr x4, [x0, #168]
	lsr x4, x4, #0
	movz x5, #1, lsl #0
	and x4, x4, x5
	orr x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	sub x3, x3, #5
	cbz x3, 2202f
	b 2203f
2202:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2203:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2187b
2186:
	ldr x3, [x0, #160]
	cbnz x3, 2204f
	b 2205f
2204:
2206:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2206b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2207f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2209:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2210:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2210b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 2209b
	b 2208f
2207:
	cbz x4, 2211f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2213:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2214b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 2213b
	b 2212f
2211:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2215:
	ldr x16, [x0, #104]
	sub x16, x17, x16
	ldr x3, [x0, #200]
	add x16, x16, x3
	movi v23.2d, #0
	movz x14, #32, lsl #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
2216:
	cmeq v20.2d, v23.2d, v22.2d
	ldr q21, [x16, #0]
	bit v16.16b, v21.16b, v20.16b
	ldr q21, [x16, #16]
	bit v17.16b, v21.16b, v20.16b
	ldr q21, [x16, #32]
	bit v18.16b, v21.16b, v20.16b
	ldr q21, [x16, #48]
	bit v19.16b, v21.16b, v20.16b
	add x16, x16, x6
	add v23.2d, v23.2d, v24.2d
	sub x14, x14, #1
	cbnz x14, 2216b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2215b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2212:
2208:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2205:
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2218:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2219b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2220:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2220b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2221:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2222:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2223:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	ldr x3, [x0, #176]
	cbnz x3, 2218b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2224:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2224b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2225:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2226:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2227:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2228f
	b 2229f
2228:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2229:
	cbnz x2, 2227b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2230:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2231b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2232:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2232b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2233:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2234:
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
	cbnz x14, 2234b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2233b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2235:
	and x5, x2, x6
	cbz x5, 2236f
	b 2237f
2236:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2237:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2235b
	ldr x0, [x0, #176]
	movz x3, #1, lsl #0
	and x0, x0, x3
	b 23f
22:
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
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2238:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2239f
	b 2240f
2239:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2240:
	cbnz x2, 2238b
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
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2241:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2242f
	b 2243f
2242:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2243:
	cbnz x2, 2241b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2244:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2244b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #176]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2245b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2246f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2248:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2248b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2249:
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
	cbnz x13, 2249b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2250:
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
2251:
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
	cbnz x14, 2251b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2252f
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2254:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2253f
2252:
2253:
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2250b
	b 2247f
2246:
	ldr x12, [x0, #48]
	sub x13, x12, #2
	cbz x13, 2255f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #24
	add x13, x9, x13
	ldr x15, [x13, #16]
	ldr x3, [x13, #8]
	ldr x4, [x13, #0]
	movz x10, #1, lsl #0
	movz x13, #63, lsl #0
2257:
	add x16, x15, x15
	add x17, x10, x10
	tst x15, x15
	csel x15, x16, x15, pl
	csel x10, x17, x10, pl
	sub x13, x13, #1
	cbnz x13, 2257b
	mul x16, x3, x10
	umulh x4, x4, x10
	add x16, x16, x4
	umulh x3, x3, x10
	add x15, x15, x3
	str x10, [x6, #8]
	str x15, [x6, #16]
	str x16, [x6, #24]
	ldr x5, [x6, #16]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2258:
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
	cbnz x13, 2258b
	str x10, [x6, #0]
	add x8, x11, #0
	movz x9, #1, lsl #0
	sub x13, x12, #1
	add x16, x8, #0
	add x14, x12, #2
2259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2259b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	add x13, x12, #1
	str x13, [x0, #208]
2260:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x2, [x16, #16]
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	ldr x17, [x6, #8]
	ldr x5, [x6, #16]
	mul x2, x2, x17
	umulh x15, x3, x17
	add x2, x2, x15
	mul x3, x3, x17
	umulh x15, x4, x17
	add x3, x3, x15
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
	sub x13, x13, #32
	add x16, x11, x13
	ldr x3, [x16, #16]
	ldr x4, [x16, #8]
	ldr x14, [x16, #0]
	sub x15, x12, #3
	tst x15, x15
	csel x14, x15, x14, eq
	ldr x17, [x6, #8]
	mul x3, x3, x17
	umulh x15, x4, x17
	add x3, x3, x15
	mul x4, x4, x17
	umulh x15, x14, x17
	add x4, x4, x15
	ldr x15, [x6, #24]
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
2261:
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
	cbnz x14, 2261b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2262f
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2264:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2264b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2263f
2262:
2263:
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2260b
	b 2256f
2255:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2265f
2267:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2267b
	b 2266f
2265:
2266:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2268:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2268b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2269:
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
2270:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2270b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2271b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2272:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2272b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2269b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2273:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2273b
2256:
2247:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_4}
	umov x30, v31.d[0]
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #160]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x5, #2, lsl #0
	subs x6, x12, x5
	csel x12, x12, x5, hs
	add x1, x0, #0
	add x0, x4, #0
	str x1, [x0, #128]
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
	add x0, x1, #0
	ldr x5, [x0, #232]
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	lsl x6, x6, #5
	add x4, x4, x6
	str x4, [x0, #240]
	ldr x12, [x0, #192]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x5, #2, lsl #0
	subs x6, x12, x5
	csel x12, x12, x5, hs
	add x1, x0, #0
	add x0, x4, #0
	str x1, [x0, #128]
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
	add x0, x1, #0
	ldr x0, [x0, #232]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2274:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2274b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2275:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2276f
	b 2277f
2276:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2277:
	cbnz x2, 2275b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2278:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2278b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2279:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2280f
	b 2281f
2280:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2281:
	cbnz x2, 2279b
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2282:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2282b
	ldr x5, [x0, #128]
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2283:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2284f
	b 2285f
2284:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2285:
	cbnz x2, 2283b
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2286:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2286b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x5, [x0, #128]
	ldr x3, [x5, #176]
	and x15, x15, x3
	str x15, [x5, #176]
	ldr x5, [x0, #128]
	ldr x5, [x5, #176]
	str x5, [x0, #192]
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	add x14, x12, #0
2287:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2287b
	movz x4, #3, lsl #0
	and x5, x15, x4
	eor x5, x5, x4
	ldr x16, [x0, #64]
	ldr x3, [x16, #0]
	orr x3, x3, x5
	str x3, [x16, #0]
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
2288:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2288b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x5, [x0, #128]
	ldr x5, [x5, #176]
	str x5, [x0, #192]
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	add x14, x12, #0
2289:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2289b
	movz x4, #3, lsl #0
	and x5, x15, x4
	eor x5, x5, x4
	ldr x16, [x0, #64]
	ldr x3, [x16, #0]
	orr x3, x3, x5
	str x3, [x16, #0]
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
2290:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2290b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x0, [x0, #128]
	ldr x5, [x0, #240]
	ldr x5, [x5, #48]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
2291:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2291b
	add x3, x3, x5
	sub x3, x3, x12
	lsl x3, x3, #6
	str x3, [x0, #248]
	ldr x12, [x0, #48]
	ldr x10, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x10, x13
	ldr x4, [x13, #0]
	cbz x4, 2292f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2294f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2296:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2296b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2295f
2294:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2297f
2299:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2299b
	b 2298f
2297:
2298:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2300:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2301f
	b 2302f
2301:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2303:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2303b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2304:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2304b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2305:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2305b
2302:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2300b
2295:
	b 2293f
2292:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2306f
2308:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2308b
	b 2307f
2306:
2307:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2309:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2310f
	b 2311f
2310:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2312:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2312b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2313:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2313b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2314:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2314b
2311:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2309b
2293:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2315:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2315b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2316:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2317:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2317b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2318:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2318b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2319:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2319b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2320:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2320b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2321:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2321b
	ldr x3, [x0, #176]
	cbnz x3, 2316b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2322:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2322b
	ldr x0, [x0, #128]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_6}
	umov x30, v31.d[0]
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2323:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2323b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2324:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2325:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2325b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2326:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2326b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2327:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2327b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2328:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2328b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2329:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2329b
	ldr x3, [x0, #176]
	cbnz x3, 2324b
	ldr x5, [x0, #128]
	ldr x3, [x5, #216]
	str x3, [x0, #136]
	ldr x3, [x5, #192]
	str x3, [x0, #144]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
	ldr x3, [x0, #120]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #200]
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2330:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2330b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #208]
	add x14, x12, #0
2331:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2331b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2332:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2332b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2333:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #208]
	add x14, x12, #0
2334:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2334b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2333b
2335:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2336:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #168]
	lsl x4, x3, #4
	str x4, [x0, #168]
	lsr x3, x3, #4
	movz x4, #15, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2337:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2338:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2338b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #16
	cbnz x4, 2337b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2336b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2335b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_7}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x5, [x0, #232]
	ldr x5, [x5, #48]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
2339:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2339b
	add x3, x3, x5
	sub x3, x3, x12
	lsl x3, x3, #6
	str x3, [x0, #248]
	ldr x12, [x0, #48]
	ldr x10, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x10, x13
	ldr x4, [x13, #0]
	cbz x4, 2340f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2342f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2344:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2344b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2343f
2342:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2345f
2347:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2347b
	b 2346f
2345:
2346:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2348:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2349f
	b 2350f
2349:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2351:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2351b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2352:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2352b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2353:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2353b
2350:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2348b
2343:
	b 2341f
2340:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2354f
2356:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2356b
	b 2355f
2354:
2355:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2357:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2358f
	b 2359f
2358:
	ldr x5, [x0, #112]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2360:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2360b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2361:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2361b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2362:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2362b
2359:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2357b
2341:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2363:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2363b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2364:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2365:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2365b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2366:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2366b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2367:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2367b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2368:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2368b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2369:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2369b
	ldr x3, [x0, #176]
	cbnz x3, 2364b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2370:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2370b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2371:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2371b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2372:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2372b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_6}
	umov x30, v31.d[0]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2373:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2373b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2374:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2375:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2375b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2376:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2376b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2377:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2377b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2378:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2378b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2379:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2379b
	ldr x3, [x0, #176]
	cbnz x3, 2374b
	ldr x5, [x0, #128]
	ldr x3, [x5, #200]
	str x3, [x0, #136]
	ldr x3, [x5, #160]
	str x3, [x0, #144]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
	ldr x3, [x0, #120]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #200]
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2380:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2380b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #208]
	add x14, x12, #0
2381:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2381b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2382:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2382b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2383:
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #208]
	add x14, x12, #0
2384:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2384b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2383b
2385:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2386:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #168]
	lsl x4, x3, #4
	str x4, [x0, #168]
	lsr x3, x3, #4
	movz x4, #15, lsl #0
	and x3, x3, x4
	str x3, [x0, #216]
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2387:
	ldr x3, [x0, #224]
	ldr x4, [x0, #216]
	eor x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x16, [x0, #208]
	ldr x17, [x0, #104]
	add x14, x12, #0
2388:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2388b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #16
	cbnz x4, 2387b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2386b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2385b
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2389:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2389b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2390:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2391:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2391b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2392:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2392b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	mov v31.d[0], x30
	bl {vg_rsa_mul_4_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_7}
	umov x30, v31.d[0]
	ldr x9, [x0, #96]
	ldr x17, [x0, #104]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2393:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2393b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2394:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2394b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2395:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2395b
	ldr x3, [x0, #176]
	cbnz x3, 2390b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2396:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2396b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2397:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2397b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2398:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2398b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2399:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2400f
	b 2401f
2400:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2401:
	cbnz x2, 2399b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2402:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2402b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2403:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2403b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2404:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2404b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2405:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2406:
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
	cbnz x14, 2406b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2405b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2407:
	and x5, x2, x6
	cbz x5, 2408f
	b 2409f
2408:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2409:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2407b
	ldr x0, [x0, #176]
	movz x3, #1, lsl #0
	and x0, x0, x3
23:
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2410:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2410b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6
