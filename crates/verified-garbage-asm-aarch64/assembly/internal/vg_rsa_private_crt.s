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
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 227f
229:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 229b
	b 228f
227:
228:
	str x13, [x0, #208]
	sub x13, x12, #1
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
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
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
	movz x13, #6, lsl #0
	str x13, [x0, #208]
235:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 235b
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
236:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
237:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 238f
	b 239f
238:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
239:
	cbnz x2, 237b
	ldr x8, [x0, #72]
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
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
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
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
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
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
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
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
248:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 248b
	ldr x5, [x0, #232]
	ldr x11, [x5, #64]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
249:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
250:
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
	cbnz x14, 250b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 249b
	ldr x12, [x0, #48]
	ldr x16, [x0, #80]
	ldr x17, [x0, #64]
	movz x9, #0, lsl #0
	add x14, x12, #0
251:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 251b
	add x14, x12, #2
252:
	ldr x3, [x16, #0]
	orr x9, x9, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 252b
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
253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 253b
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
254:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 254b
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
255:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 255b
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
256:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
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
257:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
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
258:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 258b
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
	cbz x4, 259f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 261f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
263:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 262f
261:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 264f
266:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 266b
	b 265f
264:
265:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
267:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 268f
	b 269f
268:
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
270:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
272:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 272b
269:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 267b
262:
	b 260f
259:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 273f
275:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 275b
	b 274f
273:
274:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
276:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 277f
	b 278f
277:
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
279:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 279b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
280:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 280b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
281:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 281b
278:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 276b
260:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
282:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 282b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
283:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
284:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 284b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
285:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 285b
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
286:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
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
	ldr x3, [x0, #176]
	cbnz x3, 283b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
289:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 289b
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
290:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
291:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
292:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 292b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
293:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 293b
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
294:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 294b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
295:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 295b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
296:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 296b
	ldr x3, [x0, #176]
	cbnz x3, 291b
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
297:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
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
298:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
299:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2100:
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
2101:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2100b
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
	cbnz x9, 2102f
	b 2103f
2102:
2104:
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
	cbnz x9, 2104b
2103:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2105f
	b 2106f
2105:
2107:
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
	cbz x3, 2108f
	b 2109f
2108:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2109:
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
	cbz x3, 2110f
	b 2111f
2110:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2111:
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
	cbz x3, 2112f
	b 2113f
2112:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2113:
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
	cbz x3, 2114f
	b 2115f
2114:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2115:
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
	cbz x3, 2116f
	b 2117f
2116:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2117:
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
	cbz x3, 2118f
	b 2119f
2118:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2119:
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
	cbz x3, 2120f
	b 2121f
2120:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2121:
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
	cbz x3, 2122f
	b 2123f
2122:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2123:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2107b
2106:
	ldr x3, [x0, #160]
	cbnz x3, 2124f
	b 2125f
2124:
2126:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2126b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2127f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2129:
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
2130:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2130b
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
	cbnz x4, 2129b
	b 2128f
2127:
	cbz x4, 2131f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2133:
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
2134:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2134b
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
	cbnz x4, 2133b
	b 2132f
2131:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2135:
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
2136:
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
	cbnz x14, 2136b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2135b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2132:
2128:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2125:
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
2137:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2137b
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
	cbz x4, 2138f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2140f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2142:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2141f
2140:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2143f
2145:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2145b
	b 2144f
2143:
2144:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2146:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2147f
	b 2148f
2147:
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
2149:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2150:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2151:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2151b
2148:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2146b
2141:
	b 2139f
2138:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2152f
2154:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2154b
	b 2153f
2152:
2153:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2155:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2156f
	b 2157f
2156:
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
2158:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2159:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2160:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2160b
2157:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2155b
2139:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2161:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2162:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2163:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2164:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2164b
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
2165:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
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
	ldr x3, [x0, #176]
	cbnz x3, 2162b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2168:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2168b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2169:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2169b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2170:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2170b
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
2171:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2171b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2172:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2173:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2174:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2174b
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
2175:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2175b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2176:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2177:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2177b
	ldr x3, [x0, #176]
	cbnz x3, 2172b
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
2178:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2178b
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
2179:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2180:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2180b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2181:
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
2182:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2182b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2181b
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
	cbnz x9, 2183f
	b 2184f
2183:
2185:
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
	cbnz x9, 2185b
2184:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2186f
	b 2187f
2186:
2188:
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
	cbz x3, 2189f
	b 2190f
2189:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2190:
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
	cbz x3, 2191f
	b 2192f
2191:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2192:
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
	cbz x3, 2193f
	b 2194f
2193:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2194:
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
	cbz x3, 2195f
	b 2196f
2195:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2196:
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
	cbz x3, 2197f
	b 2198f
2197:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2198:
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
	cbz x3, 2199f
	b 2200f
2199:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2200:
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
	cbz x3, 2201f
	b 2202f
2201:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2202:
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
	cbz x3, 2203f
	b 2204f
2203:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2204:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2188b
2187:
	ldr x3, [x0, #160]
	cbnz x3, 2205f
	b 2206f
2205:
2207:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2207b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2208f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2210:
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
2211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2211b
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
	cbnz x4, 2210b
	b 2209f
2208:
	cbz x4, 2212f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2214:
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
2215:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2215b
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
	cbnz x4, 2214b
	b 2213f
2212:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2216:
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
2217:
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
	cbnz x14, 2217b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2216b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2213:
2209:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
2206:
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2218b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2219:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2220:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2220b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2221:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2221b
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
2222:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2223:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2224:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2224b
	ldr x3, [x0, #176]
	cbnz x3, 2219b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2225:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2226:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2227:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2228:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2229f
	b 2230f
2229:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2230:
	cbnz x2, 2228b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2231:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2231b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2232:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2232b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2233:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2233b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2234:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2235:
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
	cbnz x14, 2235b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2234b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2236:
	and x5, x2, x6
	cbz x5, 2237f
	b 2238f
2237:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2238:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2236b
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
2239:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2240f
	b 2241f
2240:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2241:
	cbnz x2, 2239b
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
2242:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2243f
	b 2244f
2243:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2244:
	cbnz x2, 2242b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2245:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2245b
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
2246:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2246b
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
	cbz x3, 2247f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2249:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2249b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2250:
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
	cbnz x13, 2250b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2251:
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
2252:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2252b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2253:
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
	cbnz x14, 2253b
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
2254:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2255f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2257:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2257b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2256f
2255:
2256:
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2258f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2260:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2260b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 2259f
2258:
2259:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2261:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2261b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2251b
	b 2248f
2247:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2262f
2264:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2264b
	b 2263f
2262:
2263:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2265b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2266:
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
2267:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2267b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2268b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2269:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2269b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2266b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2270:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2270b
2248:
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
2271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2271b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #160]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2272:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2273f
	b 2274f
2273:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2274:
	cbnz x2, 2272b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2275:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2275b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2276:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2277f
	b 2278f
2277:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2278:
	cbnz x2, 2276b
	ldr x0, [x0, #128]
	ldr x0, [x0, #240]
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2279:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2279b
	ldr x5, [x0, #128]
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2280:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2281f
	b 2282f
2281:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2282:
	cbnz x2, 2280b
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2283b
	ldr x5, [x0, #232]
	ldr x11, [x5, #64]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2284:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2284b
	ldr x12, [x0, #48]
	ldr x16, [x0, #80]
	ldr x17, [x0, #64]
	movz x9, #0, lsl #0
	add x14, x12, #0
2286:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2286b
	add x14, x12, #2
2287:
	ldr x3, [x16, #0]
	orr x9, x9, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2287b
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
2288:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2288b
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
	ldr x0, [x0, #240]
	ldr x5, [x0, #128]
	ldr x5, [x5, #176]
	str x5, [x0, #192]
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	add x14, x12, #0
2291:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2291b
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
2292:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2292b
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
2293:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2293b
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
	cbz x4, 2294f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2296f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2298:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2298b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2297f
2296:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2299f
2301:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2301b
	b 2300f
2299:
2300:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2302:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2303f
	b 2304f
2303:
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
2305:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2305b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2306:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2306b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2307:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2307b
2304:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2302b
2297:
	b 2295f
2294:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2308f
2310:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2310b
	b 2309f
2308:
2309:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2311:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2312f
	b 2313f
2312:
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
2314:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2314b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2315:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2315b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2316:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2316b
2313:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2311b
2295:
	ldr x0, [x0, #240]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2317:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2317b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2318:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2319:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2319b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2320:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2320b
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
2321:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2321b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2322:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2322b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2323:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2323b
	ldr x3, [x0, #176]
	cbnz x3, 2318b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2324:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2324b
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
2325:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2325b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2326:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2327:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2327b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2328:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2328b
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
2329:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2329b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2330:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2330b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2331:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2331b
	ldr x3, [x0, #176]
	cbnz x3, 2326b
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
2332:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2332b
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
2333:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2333b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2334:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2334b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2335:
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
2336:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2336b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2335b
2337:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2338:
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
2339:
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
2340:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2340b
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
	cbnz x4, 2339b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2338b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2337b
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
2341:
	add x3, x3, x5
	subs x4, x3, x12
	csel x4, x7, x8, hs
	cbnz x4, 2341b
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
	cbz x4, 2342f
	ldr x13, [x0, #248]
	lsr x13, x13, #6
	sub x5, x12, #1
	subs x6, x13, x5
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x6, x8, x7, lo
	cbz x6, 2344f
	movz x9, #1, lsl #0
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2346:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2346b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_6}
	umov x30, v31.d[0]
	b 2345f
2344:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2347f
2349:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2349b
	b 2348f
2347:
2348:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2350:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2351f
	b 2352f
2351:
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
2353:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
2352:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2350b
2345:
	b 2343f
2342:
	ldr x3, [x0, #248]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2356f
2358:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2358b
	b 2357f
2356:
2357:
	str x9, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
2359:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #248]
	ldr x4, [x0, #208]
	and x3, x3, x4
	cbnz x3, 2360f
	b 2361f
2360:
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
2362:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2362b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2363:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2363b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2364:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2364b
2361:
	ldr x3, [x0, #208]
	lsr x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 2359b
2343:
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2365:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2365b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2366:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2367:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2367b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2368:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2368b
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
2369:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2369b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2370:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2370b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2371:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2371b
	ldr x3, [x0, #176]
	cbnz x3, 2366b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #112]
	add x14, x12, #0
2372:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2372b
	ldr x0, [x0, #128]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2373:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2373b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #72]
	add x14, x12, #0
2374:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2374b
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
2375:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2375b
	ldr x5, [x0, #128]
	ldr x3, [x5, #112]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2376:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2377:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2377b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2378:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2378b
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
2379:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2379b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2380:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2380b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2381:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2381b
	ldr x3, [x0, #176]
	cbnz x3, 2376b
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
2382:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2382b
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
2383:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2383b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2384:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2384b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2385:
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
2386:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2386b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2385b
2387:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2388:
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
2389:
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
2390:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2390b
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
	cbnz x4, 2389b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2388b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2387b
	ldr x0, [x0, #128]
	ldr x0, [x0, #232]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2391:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2391b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
2392:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2393:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2393b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
2394:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2394b
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
2395:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2395b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
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
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2397:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2397b
	ldr x3, [x0, #176]
	cbnz x3, 2392b
	ldr x16, [x0, #112]
	ldr x17, [x0, #96]
	ldr x13, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2398:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2398b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x5, [x0, #104]
	add x14, x12, #0
	adds x3, x7, x7
2399:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2399b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2400:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2400b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #160]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2401:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2402f
	b 2403f
2402:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2403:
	cbnz x2, 2401b
	ldr x15, [x0, #192]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	add x14, x12, #0
2404:
	ldr x3, [x16, #0]
	and x3, x3, x15
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2404b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
	ldr x0, [x0, #128]
	ldr x16, [x0, #80]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x14, x12, x12
	add x14, x14, #2
2405:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2405b
	ldr x5, [x0, #240]
	ldr x16, [x5, #112]
	ldr x12, [x5, #48]
	ldr x17, [x0, #80]
	add x14, x12, #0
2406:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2406b
	ldr x5, [x0, #232]
	ldr x11, [x5, #112]
	ldr x13, [x5, #48]
	ldr x5, [x0, #240]
	ldr x9, [x5, #64]
	ldr x12, [x5, #48]
	ldr x8, [x0, #80]
	movz x7, #0, lsl #0
2407:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2408:
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
	cbnz x14, 2408b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2407b
	ldr x8, [x0, #80]
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2409:
	and x5, x2, x6
	cbz x5, 2410f
	b 2411f
2410:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2411:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2409b
	ldr x0, [x0, #176]
	movz x3, #1, lsl #0
	and x0, x0, x3
23:
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2412:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2412b
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6
