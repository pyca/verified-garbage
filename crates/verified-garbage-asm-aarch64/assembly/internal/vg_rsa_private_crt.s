// The functions of `src/internal/vg_rsa_private_crt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt:
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
217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 217b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
218:
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
	cbnz x14, 218b
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
219:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 220f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
222:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 222b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 221f
220:
221:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 223f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
225:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 224f
223:
224:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
226:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 226b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 216b
	b 213f
212:
	ldr x12, [x0, #48]
	sub x13, x12, #2
	cbz x13, 227f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #16
	add x13, x9, x13
	ldr x15, [x13, #8]
	ldr x3, [x13, #0]
	movz x10, #1, lsl #0
	movz x13, #63, lsl #0
229:
	add x16, x15, x15
	add x17, x10, x10
	tst x15, x15
	csel x15, x16, x15, pl
	csel x10, x17, x10, pl
	sub x13, x13, #1
	cbnz x13, 229b
	umulh x3, x3, x10
	add x15, x15, x3
	str x10, [x6, #8]
	str x15, [x6, #16]
	ldr x5, [x6, #16]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
230:
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
	cbnz x13, 230b
	str x10, [x6, #0]
	add x8, x11, #0
	movz x9, #1, lsl #0
	sub x13, x12, #1
	add x16, x8, #0
	add x14, x12, #2
231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 231b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	add x13, x12, #1
	str x13, [x0, #208]
232:
	ldr x8, [x0, #80]
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
	add x16, x8, #0
	add x14, x12, #2
233:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 233b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
234:
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
	cbnz x14, 234b
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
235:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 235b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 236f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
238:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 237f
236:
237:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 239f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
241:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 241b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 240f
239:
240:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
242:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 242b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 232b
	b 228f
227:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 243f
245:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 245b
	b 244f
243:
244:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
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
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
247:
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
248:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 248b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
249:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 249b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
250:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 250b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 247b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
251:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 251b
228:
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
252:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 252b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
253:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 254f
	b 255f
254:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
255:
	cbnz x2, 253b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
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
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
260:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x5, [x0, #128]
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
261:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 262f
	b 263f
262:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
263:
	cbnz x2, 261b
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
264:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x5, [x0, #232]
	ldr x11, [x5, #64]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
265:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
266:
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
	cbnz x14, 266b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 265b
	ldr x12, [x0, #48]
	ldr x16, [x0, #80]
	ldr x17, [x0, #64]
	movz x9, #0, lsl #0
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	add x14, x12, #2
268:
	ldr x3, [x16, #0]
	orr x9, x9, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
269:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 269b
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
270:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
272:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
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
273:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
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
274:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 274b
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
	cbz x4, 275f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 277f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
279:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 279b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 278f
277:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 280f
282:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 282b
	b 281f
280:
281:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
283:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 284f
	b 285f
284:
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
286:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 286b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
287:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 287b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
288:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 288b
285:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 283b
278:
	b 276f
275:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 289f
291:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 291b
	b 290f
289:
290:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
292:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 293f
	b 294f
293:
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
295:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 295b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
296:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 296b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
297:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 297b
294:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 292b
276:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
298:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 298b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
299:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2100:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2101:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2101b
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
2102:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2103:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2104:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	ldr x3, [x0, #176]
	cbnz x3, 299b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2105:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2105b
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
2106:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2107:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2108:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2109:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2109b
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
2110:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2111:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2112:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	ldr x3, [x0, #176]
	cbnz x3, 2107b
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
2113:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2113b
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
2114:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2115:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2116:
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
2117:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2116b
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
	cbnz x9, 2118f
	b 2119f
2118:
2120:
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
	cbnz x9, 2120b
2119:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2121f
	b 2122f
2121:
2123:
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
	cbz x3, 2124f
	b 2125f
2124:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2125:
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
	cbz x3, 2126f
	b 2127f
2126:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2127:
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
	cbz x3, 2128f
	b 2129f
2128:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2129:
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
	cbz x3, 2130f
	b 2131f
2130:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2131:
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
	cbz x3, 2132f
	b 2133f
2132:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2133:
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
	cbz x3, 2134f
	b 2135f
2134:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2135:
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
	cbz x3, 2136f
	b 2137f
2136:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2137:
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
	cbz x3, 2138f
	b 2139f
2138:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2139:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2123b
2122:
	ldr x3, [x0, #160]
	cbnz x3, 2140f
	b 2141f
2140:
2142:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2142b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2143f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2145:
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
2146:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2146b
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
	cbnz x4, 2145b
	b 2144f
2143:
	cbz x4, 2147f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2149:
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
2150:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2150b
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
	cbnz x4, 2149b
	b 2148f
2147:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2151:
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
2152:
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
	cbnz x14, 2152b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2151b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2148:
2144:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2141:
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
2153:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2153b
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
	cbz x4, 2154f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2156f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2158:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2157f
2156:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2159f
2161:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2161b
	b 2160f
2159:
2160:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2162:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2163f
	b 2164f
2163:
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
2165:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2165b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2166:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2167:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2167b
2164:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2162b
2157:
	b 2155f
2154:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2168f
2170:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2170b
	b 2169f
2168:
2169:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2171:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2172f
	b 2173f
2172:
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
2174:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
2173:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2171b
2155:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2177:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2177b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2178:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2179:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2180:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2180b
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
2181:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2181b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2182:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2182b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2183:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2183b
	ldr x3, [x0, #176]
	cbnz x3, 2178b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2184:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2184b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2185:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2185b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2186:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2186b
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
2187:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2187b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2188:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2189:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2189b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2190:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2190b
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
2191:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2191b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2192:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2192b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2193:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2193b
	ldr x3, [x0, #176]
	cbnz x3, 2188b
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
2194:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2194b
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
2195:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2195b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2196:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2196b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2197:
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
2198:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2198b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2197b
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
	cbnz x9, 2199f
	b 2200f
2199:
2201:
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
	cbnz x9, 2201b
2200:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2202f
	b 2203f
2202:
2204:
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
	cbz x3, 2205f
	b 2206f
2205:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2206:
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
	cbz x3, 2207f
	b 2208f
2207:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2208:
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
	cbz x3, 2209f
	b 2210f
2209:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2210:
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
	cbz x3, 2211f
	b 2212f
2211:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2212:
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
	cbz x3, 2213f
	b 2214f
2213:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2214:
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
	cbz x3, 2215f
	b 2216f
2215:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2216:
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
	cbz x3, 2217f
	b 2218f
2217:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2218:
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
	cbz x3, 2219f
	b 2220f
2219:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2220:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2204b
2203:
	ldr x3, [x0, #160]
	cbnz x3, 2221f
	b 2222f
2221:
2223:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2223b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2224f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2226:
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
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2227b
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
	cbnz x4, 2226b
	b 2225f
2224:
	cbz x4, 2228f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2230:
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
2231:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2231b
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
	cbnz x4, 2230b
	b 2229f
2228:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2232:
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
2233:
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
	cbnz x14, 2233b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2232b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2229:
2225:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2222:
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2234:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2234b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2235:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2236:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2236b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2237:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2237b
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
2238:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2238b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2239:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2239b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2240:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2240b
	ldr x3, [x0, #176]
	cbnz x3, 2235b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2241:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2241b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2242:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2242b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2243:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2243b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2244:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2245f
	b 2246f
2245:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2246:
	cbnz x2, 2244b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2247:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2247b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2248:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2248b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2249:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2249b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2250:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2251:
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
	cbnz x14, 2251b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2250b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2252:
	and x5, x2, x6
	cbz x5, 2253f
	b 2254f
2253:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2254:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2252b
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
2255:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2256f
	b 2257f
2256:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2257:
	cbnz x2, 2255b
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
2258:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2259f
	b 2260f
2259:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2260:
	cbnz x2, 2258b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2261:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2261b
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
2262:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2262b
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
	cbz x3, 2263f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2265:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2265b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2266:
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
	cbnz x13, 2266b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2267:
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
2268:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2268b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2269:
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
	cbnz x14, 2269b
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
2270:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2270b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2271f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2273:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2273b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2272f
2271:
2272:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2274f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2276:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2276b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2275f
2274:
2275:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2277:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2277b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2267b
	b 2264f
2263:
	ldr x12, [x0, #48]
	sub x13, x12, #2
	cbz x13, 2278f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #16
	add x13, x9, x13
	ldr x15, [x13, #8]
	ldr x3, [x13, #0]
	movz x10, #1, lsl #0
	movz x13, #63, lsl #0
2280:
	add x16, x15, x15
	add x17, x10, x10
	tst x15, x15
	csel x15, x16, x15, pl
	csel x10, x17, x10, pl
	sub x13, x13, #1
	cbnz x13, 2280b
	umulh x3, x3, x10
	add x15, x15, x3
	str x10, [x6, #8]
	str x15, [x6, #16]
	ldr x5, [x6, #16]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2281:
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
	cbnz x13, 2281b
	str x10, [x6, #0]
	add x8, x11, #0
	movz x9, #1, lsl #0
	sub x13, x12, #1
	add x16, x8, #0
	add x14, x12, #2
2282:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2282b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	add x13, x12, #1
	str x13, [x0, #208]
2283:
	ldr x8, [x0, #80]
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
	add x16, x8, #0
	add x14, x12, #2
2284:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2284b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2285:
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
	cbnz x14, 2285b
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
2286:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2286b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2287f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2289:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2289b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2288f
2287:
2288:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2290f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2292:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2292b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2291f
2290:
2291:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2293:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2293b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2283b
	b 2279f
2278:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2294f
2296:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2296b
	b 2295f
2294:
2295:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2297:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2297b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2298:
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
2299:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2299b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2300:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2300b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2301:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2301b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2298b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2302:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2302b
2279:
2264:
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
2303:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2303b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2304:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2305f
	b 2306f
2305:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2306:
	cbnz x2, 2304b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2307:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2307b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2308:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2309f
	b 2310f
2309:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2310:
	cbnz x2, 2308b
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2311:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2311b
	ldr x5, [x0, #128]
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2312:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2313f
	b 2314f
2313:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2314:
	cbnz x2, 2312b
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2315:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2315b
	ldr x5, [x0, #232]
	ldr x11, [x5, #64]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2316:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2317:
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
	cbnz x14, 2317b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2316b
	ldr x12, [x0, #48]
	ldr x16, [x0, #80]
	ldr x17, [x0, #64]
	movz x9, #0, lsl #0
	add x14, x12, #0
2318:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2318b
	add x14, x12, #2
2319:
	ldr x3, [x16, #0]
	orr x9, x9, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2319b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #176]
	and x15, x15, x3
	str x15, [x0, #176]
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2320:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2320b
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
2321:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2321b
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
2322:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2322b
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
2323:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2323b
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
2324:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2324b
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
2325:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2325b
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
	cbz x4, 2326f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2328f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2330:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2330b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2329f
2328:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2331f
2333:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2333b
	b 2332f
2331:
2332:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2334:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2335f
	b 2336f
2335:
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
2337:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2337b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2338:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2338b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2339:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2339b
2336:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2334b
2329:
	b 2327f
2326:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2340f
2342:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2342b
	b 2341f
2340:
2341:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2343:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2344f
	b 2345f
2344:
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
2346:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2346b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2347:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2347b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2348:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2348b
2345:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2343b
2327:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2349:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2349b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2350:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2351:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2351b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2352:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2352b
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
2353:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2353b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2354:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2354b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2355:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2355b
	ldr x3, [x0, #176]
	cbnz x3, 2350b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2356:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2356b
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
2357:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2357b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2358:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2359:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2359b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2360:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2360b
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
2361:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2361b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2362:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2362b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2363:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2363b
	ldr x3, [x0, #176]
	cbnz x3, 2358b
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
2364:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2364b
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
2365:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2365b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2366:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2366b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2367:
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
2368:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2368b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2367b
2369:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2370:
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
2371:
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
2372:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2372b
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
	cbnz x4, 2371b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2370b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2369b
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
2373:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2373b
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
	cbz x4, 2374f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2376f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2378:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2378b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2377f
2376:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2379f
2381:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2381b
	b 2380f
2379:
2380:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2382:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2383f
	b 2384f
2383:
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
2385:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2385b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2386:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2386b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2387:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2387b
2384:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2382b
2377:
	b 2375f
2374:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2388f
2390:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2390b
	b 2389f
2388:
2389:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2391:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2392f
	b 2393f
2392:
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
2394:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2394b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2395:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2395b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2396:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2396b
2393:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2391b
2375:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2397:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2397b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2398:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2399:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2399b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2400:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2400b
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
2401:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2401b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2402:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2402b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2403:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2403b
	ldr x3, [x0, #176]
	cbnz x3, 2398b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2404:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2404b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2405:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2405b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2406:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2406b
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
2407:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2407b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2408:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2409:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2409b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2410:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2410b
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
2411:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2411b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2412:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2412b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2413:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2413b
	ldr x3, [x0, #176]
	cbnz x3, 2408b
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
2414:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2414b
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
2415:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2415b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2416:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2416b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2417:
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
2418:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2418b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2417b
2419:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2420:
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
2421:
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
2422:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2422b
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
	cbnz x4, 2421b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2420b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2419b
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2423:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2423b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2424:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2425:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2425b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2426:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2426b
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
2427:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2427b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2428:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2428b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2429:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2429b
	ldr x3, [x0, #176]
	cbnz x3, 2424b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2430:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2430b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2431:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2431b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2432:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2432b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2433:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2434f
	b 2435f
2434:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2435:
	cbnz x2, 2433b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2436:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2436b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2437:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2437b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2438:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2438b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2439:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2440:
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
	cbnz x14, 2440b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2439b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2441:
	and x5, x2, x6
	cbz x5, 2442f
	b 2443f
2442:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2443:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2441b
	ldr x0, [x0, #176]
	movz x3, #1, lsl #0
	and x0, x0, x3
23:
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2444:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2444b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6
