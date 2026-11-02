// The functions of `src/ffdh.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_generate_key_precompute:
	str x0, [x5, #128]
	str x2, [x5, #136]
	str x3, [x5, #152]
	str x4, [x5, #144]
	add x0, x5, #0
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	ldr x3, [x0, #152]
	lsl x4, x2, #1
	subs x3, x3, x4
	add x4, x1, x4
	csel x1, x1, x4, eq
	movz x10, #0, lsl #0
20:
	ldrb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbz x3, 20b
	lsl x2, x2, #3
21:
	add x10, x10, #1
	lsr x3, x3, #1
	cbnz x3, 21b
	add x10, x10, x2
	str x10, [x0, #160]
	adrp x4, {VG_FFDH_VETTED_GROUPS_A64}
	add x4, x4, {VG_FFDH_VETTED_GROUPS_A64}
	movz x7, #10, lsl #0
22:
	ldr w5, [x4, #0]
	ldr w6, [x4, #4]
	add x4, x4, #8
	ldr x3, [x0, #144]
	sub x3, x3, x5
	cbz x3, 23f
	b 24f
23:
	ldr x1, [x0, #136]
	ldr x5, [x0, #152]
	add x2, x4, #0
	movz x11, #0, lsl #0
25:
	ldrb w8, [x1, #0]
	ldrb w9, [x2, #0]
	eor x8, x8, x9
	orr x11, x11, x8
	add x1, x1, #1
	add x2, x2, #1
	sub x5, x5, #1
	cbnz x5, 25b
	cbz x11, 26f
	b 27f
26:
	ldr x10, [x0, #160]
	subs x9, x10, x6
	csel x10, x6, x10, hs
	str x10, [x0, #160]
	movz x7, #1, lsl #0
27:
24:
	sub x2, x4, #8
	ldr w5, [x2, #0]
	lsl x3, x5, #1
	add x3, x3, x5
	add x4, x4, x3
	sub x7, x7, #1
	cbnz x7, 22b
	ldr x10, [x0, #160]
	add x11, x10, #7
	lsr x11, x11, #3
	str x11, [x0, #168]
	add x12, x10, #4
	movz x13, #0, lsl #0
28:
	sub x12, x12, #5
	add x13, x13, #1
	movz x14, #5, lsl #0
	subs x14, x12, x14
	lsr x14, x14, #63
	cbz x14, 28b
	str x13, [x0, #176]
	ldr x8, [x0, #128]
	str x10, [x8, #0]
	str x11, [x8, #8]
	str x13, [x8, #16]
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
	cbz x4, 29f
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
	b 210f
29:
	add x5, x8, x2
214:
	ldr x3, [x1, #0]
	rev x3, x3
	sub x5, x5, #8
	str x3, [x5, #0]
	add x1, x1, #8
	sub x2, x2, #8
	cbnz x2, 214b
210:
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
	cbz x3, 215f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
217:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 217b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
218:
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
	cbnz x13, 218b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
219:
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
220:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 220b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
221:
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
	cbnz x14, 221b
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
222:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 222b
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
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 226f
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
228:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	b 227f
226:
227:
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
229:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 229b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 219b
	b 216f
215:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 230f
232:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 232b
	b 231f
230:
231:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
233:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 233b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
234:
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
235:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
236:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
237:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 234b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
238:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 238b
216:
	ldr x17, [x0, #128]
	add x17, x17, #24
	ldr x16, [x0, #64]
	ldr x12, [x0, #48]
	add x14, x12, #0
239:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 239b
	ldr x16, [x0, #96]
	ldr x12, [x0, #48]
	add x14, x12, #0
240:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
241:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 241b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 242f
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
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	add x13, x12, #0
245:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
246:
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
	cbnz x14, 246b
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
247:
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
	cbnz x14, 247b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 245b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
249:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 249b
	b 243f
242:
	cbz x4, 250f
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
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
258:
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
	cbnz x14, 258b
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
	ldr x8, [x0, #96]
	lsr x12, x12, #3
259:
	ldr x17, [x0, #96]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
260:
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
	cbnz x15, 260b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 259b
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
	ldr x9, [x0, #96]
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
261:
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
262:
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
	cbnz x15, 262b
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
	cbnz x12, 261b
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
263:
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
	cbnz x14, 263b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
264:
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
	cbnz x14, 264b
251:
243:
	movz x3, #0, lsl #0
	ldr x17, [x0, #128]
	ldr x12, [x0, #48]
	add x3, x3, #2
	mul x3, x3, x12
	lsl x3, x3, #3
	add x17, x17, x3
	add x17, x17, #24
	ldr x16, [x0, #112]
	add x14, x12, #0
265:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	add x1, x1, x2
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
266:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 267f
	b 268f
267:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
268:
	cbnz x2, 266b
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 269f
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
	add x13, x12, #0
272:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
273:
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
	cbnz x14, 273b
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
274:
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
	cbnz x14, 274b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 272b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
275:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 275b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
276:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 276b
	b 270f
269:
	cbz x4, 277f
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
279:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 279b
	add x13, x12, #0
280:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
281:
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
	cbnz x14, 281b
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
282:
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
	cbnz x14, 282b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 280b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
283:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
284:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 284b
	b 278f
277:
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
285:
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
	cbnz x14, 285b
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
286:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #96]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
287:
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
	cbnz x15, 287b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 286b
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
288:
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
289:
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
	cbnz x15, 289b
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
	cbnz x12, 288b
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
290:
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
	cbnz x14, 290b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
291:
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
	cbnz x14, 291b
278:
270:
	movz x3, #1, lsl #0
	ldr x17, [x0, #128]
	ldr x12, [x0, #48]
	add x3, x3, #2
	mul x3, x3, x12
	lsl x3, x3, #3
	add x17, x17, x3
	add x17, x17, #24
	ldr x16, [x0, #104]
	add x14, x12, #0
292:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	movz x3, #2, lsl #0
	str x3, [x0, #216]
293:
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	add x14, x12, #0
294:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 294b
	ldr x3, [x0, #176]
	str x3, [x0, #208]
295:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #208]
	sub x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 295b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #104]
	add x14, x12, #0
296:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 296b
	ldr x3, [x0, #216]
	ldr x17, [x0, #128]
	ldr x12, [x0, #48]
	add x3, x3, #2
	mul x3, x3, x12
	lsl x3, x3, #3
	add x17, x17, x3
	add x17, x17, #24
	ldr x16, [x0, #104]
	add x14, x12, #0
297:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	movz x3, #1, lsl #0
	str x3, [x0, #232]
298:
	ldr x3, [x0, #232]
	ldr x17, [x0, #128]
	ldr x12, [x0, #48]
	add x3, x3, #2
	mul x3, x3, x12
	lsl x3, x3, #3
	add x17, x17, x3
	add x17, x17, #24
	add x16, x17, #0
	ldr x17, [x0, #72]
	add x14, x12, #0
299:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2100f
	ldr x8, [x0, #80]
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2102:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	add x13, x12, #0
2103:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2104:
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
	cbnz x14, 2104b
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
2105:
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
	cbnz x14, 2105b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2103b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2106:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2107:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	b 2101f
2100:
	cbz x4, 2108f
	ldr x8, [x0, #80]
	ldr x9, [x0, #72]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	add x13, x12, #0
2111:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2112:
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
	cbnz x14, 2112b
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
2113:
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
	cbnz x14, 2113b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2111b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2114:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2115:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	b 2109f
2108:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #104]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
2116:
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
	cbnz x14, 2116b
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
	ldr x8, [x0, #104]
	lsr x12, x12, #3
2117:
	ldr x17, [x0, #104]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #72]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
2118:
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
	cbnz x15, 2118b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2117b
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
	ldr x9, [x0, #104]
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
2119:
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
2120:
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
	cbnz x15, 2120b
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
	cbnz x12, 2119b
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
2121:
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
	cbnz x14, 2121b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2122:
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
	cbnz x14, 2122b
2109:
2101:
	ldr x3, [x0, #232]
	ldr x4, [x0, #216]
	add x3, x3, x4
	ldr x17, [x0, #128]
	ldr x12, [x0, #48]
	add x3, x3, #2
	mul x3, x3, x12
	lsl x3, x3, #3
	add x17, x17, x3
	add x17, x17, #24
	ldr x16, [x0, #112]
	add x14, x12, #0
2123:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2123b
	ldr x3, [x0, #232]
	add x3, x3, #1
	str x3, [x0, #232]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	cbnz x3, 298b
	ldr x3, [x0, #216]
	lsl x3, x3, #1
	str x3, [x0, #216]
	sub x3, x3, #32
	cbnz x3, 293b
	movz x0, #1, lsl #0
	ret
	.p2align 6

vg_ffdh_generate_key_cached:
	ldr x8, [sp, #8]
	ldr x9, [sp, #24]
	str x0, [x8, #184]
	str x2, [x8, #192]
	str x4, [x8, #136]
	str x5, [x8, #152]
	str x6, [x8, #144]
	str x7, [x8, #200]
	str x9, [x8, #128]
	add x0, x8, #0
	ldr x10, [x9, #0]
	ldr x11, [x9, #8]
	ldr x12, [x9, #16]
	str x10, [x0, #160]
	str x11, [x0, #168]
	str x12, [x0, #176]
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
	ldr x16, [x0, #128]
	add x16, x16, #24
	ldr x17, [x0, #64]
	ldr x12, [x0, #48]
	add x14, x12, #0
20:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 20b
	ldr x17, [x0, #96]
	ldr x12, [x0, #48]
	add x14, x12, #0
21:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 21b
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
	ldr x3, [x0, #160]
	sub x3, x3, #1
	movz x4, #7, lsl #0
	and x3, x3, x4
	sub x3, x4, x3
	movz x12, #255, lsl #0
	cbz x3, 22f
24:
	lsr x12, x12, #1
	sub x3, x3, #1
	cbnz x3, 24b
	b 23f
22:
23:
	str x12, [x0, #248]
	ldr x10, [x0, #144]
	ldr x11, [x0, #168]
	sub x11, x10, x11
	ldr x2, [x0, #184]
	ldr x1, [x0, #200]
	movz x13, #255, lsl #0
	movz x7, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x14, [x0, #144]
25:
	ldrb w4, [x1, #0]
	subs x5, x10, x11
	csel x6, x13, x7, hs
	eor x5, x10, x11
	movz x8, #1, lsl #0
	subs x5, x5, x8
	csel x6, x6, x12, hs
	and x4, x4, x6
	strb w4, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	add x10, x10, #1
	sub x14, x14, #1
	cbnz x14, 25b
	ldr x1, [x0, #184]
	ldr x2, [x0, #144]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
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
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x9, #0, lsl #0
29:
	ldr x3, [x8, #0]
	orr x9, x9, x3
	add x8, x8, #8
	sub x12, x12, #1
	cbnz x12, 29b
	movz x3, #0, lsl #0
	movz x4, #1, lsl #0
	subs x9, x9, x3
	csel x9, x3, x4, eq
	str x9, [x0, #224]
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	ldr x3, [x0, #152]
	lsl x4, x2, #1
	sub x3, x3, x4
	cbz x3, 210f
	add x1, x1, x4
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
212:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 213f
	b 214f
213:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
214:
	cbnz x2, 212b
	b 211f
210:
	ldr x12, [x0, #48]
	ldr x16, [x0, #64]
	ldr x17, [x0, #104]
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 215b
	ldr x8, [x0, #104]
	ldr x3, [x8, #0]
	sub x3, x3, #1
	str x3, [x8, #0]
211:
	ldr x16, [x0, #72]
	ldr x17, [x0, #104]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
216:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 216b
	movz x4, #1, lsl #0
	csel x9, x7, x4, hs
	ldr x3, [x0, #224]
	and x9, x9, x3
	cbz x9, 217f
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 219b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 220f
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
222:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	add x13, x12, #0
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
225:
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
	cbnz x14, 225b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 223b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
226:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 226b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
227:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 227b
	b 221f
220:
	cbz x4, 228f
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
230:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 230b
	add x13, x12, #0
231:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
233:
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
	cbnz x14, 233b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 231b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
234:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
235:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 235b
	b 229f
228:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
236:
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
	cbnz x14, 236b
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
	ldr x8, [x0, #96]
	lsr x12, x12, #3
237:
	ldr x17, [x0, #96]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
238:
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
	cbnz x15, 238b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 237b
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
	ldr x9, [x0, #96]
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
239:
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
240:
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
	cbnz x15, 240b
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
	cbnz x12, 239b
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
241:
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
	cbnz x14, 241b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
242:
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
	cbnz x14, 242b
229:
221:
	ldr x3, [x0, #176]
	str x3, [x0, #208]
	ldr x3, [x0, #128]
	ldr x4, [x0, #48]
	lsl x4, x4, #4
	add x3, x3, x4
	add x3, x3, #24
	str x3, [x0, #240]
243:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x1, [x0, #184]
	ldr x2, [x0, #144]
	ldr x9, [x0, #208]
	sub x9, x9, #1
	ldr x4, [x0, #176]
	ldr x5, [x0, #160]
	movz x16, #0, lsl #0
	sub x8, x9, x5
	lsr x8, x8, #63
	cbnz x8, 244f
	movz x11, #0, lsl #0
	b 245f
244:
	lsr x8, x9, #3
	sub x8, x2, x8
	sub x8, x8, #1
	add x8, x1, x8
	ldrb w11, [x8, #0]
	movz x10, #7, lsl #0
	and x10, x9, x10
	cbz x10, 246f
248:
	lsr x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 248b
	b 247f
246:
247:
	movz x10, #1, lsl #0
	and x11, x11, x10
245:
	orr x16, x16, x11
	add x9, x9, x4
	sub x8, x9, x5
	lsr x8, x8, #63
	cbnz x8, 249f
	movz x11, #0, lsl #0
	b 250f
249:
	lsr x8, x9, #3
	sub x8, x2, x8
	sub x8, x8, #1
	add x8, x1, x8
	ldrb w11, [x8, #0]
	movz x10, #7, lsl #0
	and x10, x9, x10
	cbz x10, 251f
253:
	lsr x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 253b
	b 252f
251:
252:
	movz x10, #1, lsl #0
	and x11, x11, x10
250:
	lsl x11, x11, #1
	orr x16, x16, x11
	add x9, x9, x4
	sub x8, x9, x5
	lsr x8, x8, #63
	cbnz x8, 254f
	movz x11, #0, lsl #0
	b 255f
254:
	lsr x8, x9, #3
	sub x8, x2, x8
	sub x8, x8, #1
	add x8, x1, x8
	ldrb w11, [x8, #0]
	movz x10, #7, lsl #0
	and x10, x9, x10
	cbz x10, 256f
258:
	lsr x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 258b
	b 257f
256:
257:
	movz x10, #1, lsl #0
	and x11, x11, x10
255:
	lsl x11, x11, #2
	orr x16, x16, x11
	add x9, x9, x4
	sub x8, x9, x5
	lsr x8, x8, #63
	cbnz x8, 259f
	movz x11, #0, lsl #0
	b 260f
259:
	lsr x8, x9, #3
	sub x8, x2, x8
	sub x8, x8, #1
	add x8, x1, x8
	ldrb w11, [x8, #0]
	movz x10, #7, lsl #0
	and x10, x9, x10
	cbz x10, 261f
263:
	lsr x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 263b
	b 262f
261:
262:
	movz x10, #1, lsl #0
	and x11, x11, x10
260:
	lsl x11, x11, #3
	orr x16, x16, x11
	add x9, x9, x4
	sub x8, x9, x5
	lsr x8, x8, #63
	cbnz x8, 264f
	movz x11, #0, lsl #0
	b 265f
264:
	lsr x8, x9, #3
	sub x8, x2, x8
	sub x8, x8, #1
	add x8, x1, x8
	ldrb w11, [x8, #0]
	movz x10, #7, lsl #0
	and x10, x9, x10
	cbz x10, 266f
268:
	lsr x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 268b
	b 267f
266:
267:
	movz x10, #1, lsl #0
	and x11, x11, x10
265:
	lsl x11, x11, #4
	orr x16, x16, x11
	add x9, x9, x4
	str x16, [x0, #216]
	ldr x12, [x0, #48]
	movz x9, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #104]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
269:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x9, [x0, #240]
	ldr x10, [x0, #216]
	movz x11, #0, lsl #0
270:
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	eor x3, x10, x11
	movz x7, #0, lsl #0
	subs x3, x3, x7
	sub x6, x7, #1
	csel x6, x6, x7, eq
271:
	ldr x3, [x9, #0]
	ldr x4, [x8, #0]
	and x3, x3, x6
	orr x4, x4, x3
	str x4, [x8, #0]
	add x9, x9, #8
	add x8, x8, #8
	sub x12, x12, #1
	cbnz x12, 271b
	add x11, x11, #1
	sub x3, x11, #32
	cbnz x3, 270b
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 272f
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
274:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 274b
	add x13, x12, #0
275:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
276:
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
	cbnz x14, 276b
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
277:
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
	cbnz x14, 277b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 275b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
278:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
279:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 279b
	b 273f
272:
	cbz x4, 280f
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
282:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 282b
	add x13, x12, #0
283:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
284:
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
	cbnz x14, 284b
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
285:
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
	cbnz x14, 285b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 283b
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
	b 281f
280:
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
288:
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
	cbnz x14, 288b
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
289:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
290:
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
	cbnz x15, 290b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 289b
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
291:
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
292:
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
	cbnz x15, 292b
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
	cbnz x12, 291b
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
293:
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
	cbnz x14, 293b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
294:
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
	cbnz x14, 294b
281:
273:
	ldr x3, [x0, #208]
	sub x3, x3, #1
	str x3, [x0, #208]
	cbnz x3, 243b
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 295f
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
297:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 297b
	add x13, x12, #0
298:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
299:
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
	cbnz x14, 299b
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
2100:
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
	cbnz x14, 2100b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 298b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2101:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2102:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	b 296f
295:
	cbz x4, 2103f
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
2105:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	add x13, x12, #0
2106:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2107:
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
	cbnz x14, 2107b
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
2108:
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
	cbnz x14, 2108b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2106b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2109:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2110:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	b 2104f
2103:
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
2111:
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
	cbnz x14, 2111b
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
2112:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
2113:
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
	cbnz x15, 2113b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2112b
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
2114:
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
2115:
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
	cbnz x15, 2115b
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
	cbnz x12, 2114b
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
2116:
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
	cbnz x14, 2116b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2117:
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
	cbnz x14, 2117b
2104:
296:
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2118:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	movz x4, #1, lsl #0
	csel x9, x7, x4, hs
	str x9, [x0, #224]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #72]
	add x14, x12, #0
2119:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	ldr x8, [x0, #72]
	ldr x3, [x8, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x8, #0]
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2120:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	movz x4, #1, lsl #0
	csel x9, x7, x4, hs
	ldr x3, [x0, #224]
	and x9, x9, x3
	str x9, [x0, #224]
	ldr x1, [x0, #184]
	ldr x2, [x0, #144]
	ldr x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, x3
2121:
	ldrb w3, [x1, #0]
	and x3, x3, x15
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2121b
	ldr x8, [x0, #112]
	ldr x1, [x0, #192]
	ldr x9, [x0, #144]
	add x1, x1, x9
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2122:
	and x5, x2, x6
	cbz x5, 2123f
	b 2124f
2123:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2124:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2122b
	ldr x9, [x0, #224]
	movz x0, #3, lsl #0
	lsl x9, x9, #1
	sub x0, x0, x9
	b 218f
217:
	ldr x1, [x0, #184]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2125:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2125b
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2126:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2126b
	movz x0, #2, lsl #0
218:
	ret
	.p2align 6

vg_ffdh_generate_key_search_cached:
	add x14, sp, #0
	ldr x8, [x14, #32]
	ldr x9, [x14, #0]
	ldr x10, [x14, #8]
	ldr x11, [x14, #16]
	ldr x12, [x14, #24]
	str x19, [x8, #32]
	add x19, x8, #0
	movz x13, #0, lsl #0
	str x0, [x19, #40]
	str x2, [x19, #48]
	str x5, [x19, #56]
	str x6, [x19, #64]
	str x9, [x19, #72]
	str x10, [x19, #80]
	str x13, [x19, #88]
	str x11, [x19, #96]
	str x12, [x19, #104]
	str x4, [x19, #120]
	str x30, [sp, #-16]!
20:
	ldr x9, [x19, #0]
	cbz x9, 21f
	ldr x9, [x19, #8]
	cbz x9, 23f
	ldr x9, [x19, #80]
	ldr x10, [x19, #16]
	movz x13, #0, lsl #0
	movz x14, #1, lsl #0
	subs x11, x9, x10
	csel x12, x14, x13, hs
	cbz x12, 25f
	sub sp, sp, #48
	ldr x12, [sp, #104]
	ldr x13, [sp, #112]
	ldr x0, [x19, #40]
	ldr x1, [x19, #16]
	ldr x2, [x19, #48]
	ldr x3, [x19, #16]
	ldr x4, [x19, #56]
	ldr x5, [x19, #64]
	ldr x6, [x19, #16]
	ldr x7, [x19, #72]
	ldr x9, [x19, #96]
	ldr x10, [x19, #104]
	add x11, sp, #0
	str x1, [x11, #0]
	str x9, [x11, #8]
	str x10, [x11, #16]
	str x12, [x11, #24]
	str x13, [x11, #32]
	bl {vg_ffdh_generate_key_cached}
	add sp, sp, #48
	add w9, w0, #0
	ldr x11, [x19, #16]
	ldr x12, [x19, #72]
	ldr x13, [x19, #80]
	ldr x14, [x19, #88]
	add x12, x12, x11
	sub x13, x13, x11
	add x14, x14, x11
	str x12, [x19, #72]
	str x13, [x19, #80]
	str x14, [x19, #88]
	sub x10, x9, #1
	cbz x10, 27f
	sub x10, x9, #2
	cbz x10, 29f
	sub x10, x9, #3
	cbz x10, 211f
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
213:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 213b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
214:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 214b
	b 212f
211:
	ldr x10, [x19, #0]
	sub x10, x10, #1
	movz x11, #128, lsl #0
	movz x12, #4, lsl #0
	str x10, [x19, #0]
	str x11, [x19, #8]
	str x12, [x19, #112]
212:
	b 210f
29:
	ldr x10, [x19, #8]
	sub x10, x10, #1
	movz x11, #4, lsl #0
	str x10, [x19, #8]
	str x11, [x19, #112]
210:
	b 28f
27:
	movz x10, #0, lsl #0
	movz x11, #1, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
28:
	b 26f
25:
	ldr x10, [x19, #16]
	movz x11, #0, lsl #0
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
215:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 215b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
216:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 216b
26:
	b 24f
23:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
217:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 217b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
218:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 218b
24:
	b 22f
21:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
219:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 219b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
220:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 220b
22:
	ldr x9, [x19, #112]
	sub x9, x9, #4
	cbz x9, 20b
	ldr x30, [sp], #16
	ldr x1, [x19, #120]
	ldr x2, [x19, #88]
	ldr x0, [x19, #112]
	ldr x19, [x19, #32]
	str x2, [x1, #0]
	ret
	.p2align 6

vg_ffdh_check_public:
	str x0, [x5, #128]
	str x1, [x5, #136]
	str x2, [x5, #144]
	str x3, [x5, #152]
	add x0, x5, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
27:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 27b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
28:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 29f
	b 210f
29:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
210:
	cbnz x2, 28b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #104]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 211b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
212:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 212b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
213:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 213b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 214f
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 216f
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
218:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 218b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 219f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
221:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 221b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
222:
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
	cbnz x13, 222b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
223:
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
224:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 224b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
225:
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
	cbnz x14, 225b
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
226:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 226b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
227:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 227b
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
228:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
229:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 229b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 223b
	b 220f
219:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 230f
232:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 232b
	b 231f
230:
231:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
233:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 233b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
234:
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
235:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
236:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
237:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 234b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
238:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 238b
220:
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
239:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 239b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
240:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 241f
	b 242f
241:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
242:
	cbnz x2, 240b
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
243:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 243b
	add x13, x12, #0
244:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
246:
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
	cbnz x14, 246b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 244b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
247:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
248:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 248b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
	add x13, x12, #0
250:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
251:
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
	cbnz x14, 251b
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
252:
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
	cbnz x14, 252b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 250b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
254:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
256:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x5, [x0, #128]
	ldr x3, [x5, #184]
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
257:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 257b
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
258:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
259:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 259b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
260:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
261:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
	add x13, x12, #0
262:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
263:
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
	cbnz x14, 263b
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
264:
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
	cbnz x14, 264b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 262b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
266:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 266b
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
267:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 260b
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
	cbnz x9, 268f
	b 269f
268:
270:
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
	cbnz x9, 270b
269:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 271f
	b 272f
271:
273:
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
	cbz x3, 274f
	b 275f
274:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
275:
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
	cbz x3, 276f
	b 277f
276:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
277:
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
	cbz x3, 278f
	b 279f
278:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
279:
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
	cbz x3, 280f
	b 281f
280:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
281:
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
	cbz x3, 282f
	b 283f
282:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
283:
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
	cbz x3, 284f
	b 285f
284:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
285:
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
	cbz x3, 286f
	b 287f
286:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
287:
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
	cbz x3, 288f
	b 289f
288:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
289:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 273b
272:
	ldr x3, [x0, #160]
	cbnz x3, 290f
	b 291f
290:
292:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 292b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 293f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
295:
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
296:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
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
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 295b
	b 294f
293:
	cbz x4, 297f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
299:
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
2100:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
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
	cbnz x4, 299b
	b 298f
297:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2101:
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
2102:
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
	cbnz x14, 2102b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2101b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
298:
294:
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
2103:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	add x13, x12, #0
2104:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2105:
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
	cbnz x14, 2105b
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
2106:
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
	cbnz x14, 2106b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2104b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2107:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2108:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2108b
291:
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
2109:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	add x13, x12, #0
2110:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2111:
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
	cbnz x14, 2111b
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
2112:
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
	cbnz x14, 2112b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2110b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2113:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2114:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2115:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	movz x9, #0, lsl #0
	add x14, x12, #0
2116:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x9, x8
	csel x9, x7, x8, hs
	add x0, x9, #0
	b 217f
216:
	movz x0, #1, lsl #0
217:
	b 215f
214:
	movz x0, #0, lsl #0
215:
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_check_domain:
	str x0, [x3, #136]
	str x1, [x3, #152]
	str x2, [x3, #144]
	str x4, [x3, #128]
	add x0, x3, #0
	movz x10, #4095, lsl #0
	str x10, [x0, #160]
	adrp x4, {VG_FFDH_VETTED_GROUPS_A64}
	add x4, x4, {VG_FFDH_VETTED_GROUPS_A64}
	movz x7, #10, lsl #0
20:
	ldr w5, [x4, #0]
	ldr w6, [x4, #4]
	add x4, x4, #8
	ldr x3, [x0, #144]
	sub x3, x3, x5
	cbz x3, 21f
	b 22f
21:
	ldr x1, [x0, #136]
	ldr x5, [x0, #152]
	add x2, x4, #0
	movz x11, #0, lsl #0
23:
	ldrb w8, [x1, #0]
	ldrb w9, [x2, #0]
	eor x8, x8, x9
	orr x11, x11, x8
	add x1, x1, #1
	add x2, x2, #1
	sub x5, x5, #1
	cbnz x5, 23b
	cbz x11, 24f
	b 25f
24:
	ldr x10, [x0, #160]
	subs x9, x10, x6
	csel x10, x6, x10, hs
	str x10, [x0, #160]
	movz x7, #1, lsl #0
25:
22:
	sub x2, x4, #8
	ldr w5, [x2, #0]
	lsl x3, x5, #1
	add x3, x3, x5
	add x4, x4, x3
	sub x7, x7, #1
	cbnz x7, 20b
	ldr x10, [x0, #160]
	sub x10, x10, #4095
	cbnz x10, 26f
	ldr x1, [x0, #152]
	ldr x2, [x0, #144]
	ldr x4, [x0, #128]
	add x3, x0, #0
	ldr x0, [x0, #136]
	str x0, [x3, #128]
	str x1, [x3, #136]
	str x2, [x3, #144]
	add x0, x3, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	cbz x9, 28f
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
215:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	ldr x5, [x0, #128]
	ldr x1, [x5, #216]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
216:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 217f
	b 218f
217:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
218:
	cbnz x2, 216b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #104]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
219:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
220:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 220b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
221:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 221b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 222f
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 224f
	ldr x0, [x0, #232]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
226:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 226b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
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
	ldr x16, [x0, #104]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x9, x3, x4
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #104]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
230:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
231:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 231b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
232:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 232b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 233f
	ldr x0, [x0, #128]
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
235:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 235b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
236:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	ldr x8, [x0, #72]
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
	ldr x3, [x8, #0]
	sub x3, x3, #1
	str x3, [x8, #0]
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
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
	ldr x1, [x5, #184]
	ldr x2, [x5, #192]
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
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x8, [x0, #96]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x5, [x0, #128]
	ldr x3, [x5, #72]
	str x3, [x0, #184]
	ldr x3, [x5, #48]
	str x3, [x0, #176]
246:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
247:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x3, [x0, #176]
	ldr x12, [x0, #48]
	subs x4, x3, x12
	csel x12, x12, x3, hs
	ldr x16, [x0, #184]
	ldr x17, [x0, #72]
	add x14, x12, #0
248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 248b
	str x16, [x0, #184]
	ldr x3, [x0, #176]
	sub x3, x3, x12
	str x3, [x0, #176]
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
	add x13, x12, #0
250:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
251:
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
	cbnz x14, 251b
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
252:
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
	cbnz x14, 252b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 250b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
254:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
255:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 255b
	add x13, x12, #0
256:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
258:
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
	cbnz x14, 258b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 256b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
259:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
260:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 260b
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
261:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
262:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 262b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
263:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 263b
	ldr x3, [x0, #176]
	cbnz x3, 246b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #120]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
264:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 264b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	cbz x9, 265f
	ldr x0, [x0, #128]
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
267:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
268:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 269f
	b 270f
269:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
270:
	cbnz x2, 268b
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
	cbz x3, 272f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
274:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 274b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
275:
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
	cbnz x13, 275b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
276:
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
277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 277b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
278:
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
	cbnz x14, 278b
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
279:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
280:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 280b
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
281:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 281b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
282:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 282b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 276b
	b 273f
272:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 283f
285:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 285b
	b 284f
283:
284:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
286:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 286b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
287:
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
288:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 288b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
289:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 289b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
290:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 287b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
291:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 291b
273:
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
292:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 292b
	ldr x5, [x0, #128]
	ldr x1, [x5, #216]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
293:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 294f
	b 295f
294:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
295:
	cbnz x2, 293b
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
296:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 296b
	add x13, x12, #0
297:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
298:
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
	cbnz x14, 298b
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
299:
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
	cbnz x14, 299b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 297b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2100:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2101:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2102:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	add x13, x12, #0
2103:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2104:
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
	cbnz x14, 2104b
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
2105:
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
	cbnz x14, 2105b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2103b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2106:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2107:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
2108:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
2109:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	ldr x5, [x0, #128]
	ldr x3, [x5, #184]
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
2110:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2110b
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
2111:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2112:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2113:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2114:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	add x13, x12, #0
2115:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2116:
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
	cbnz x14, 2116b
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
2117:
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
	cbnz x14, 2117b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2115b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2118:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2119:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2119b
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
2120:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2113b
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
	cbnz x9, 2121f
	b 2122f
2121:
2123:
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
	cbnz x9, 2123b
2122:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2124f
	b 2125f
2124:
2126:
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
	cbz x3, 2127f
	b 2128f
2127:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2128:
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
	cbz x3, 2129f
	b 2130f
2129:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2130:
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
	cbz x3, 2131f
	b 2132f
2131:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2132:
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
	cbz x3, 2133f
	b 2134f
2133:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2134:
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
	cbz x3, 2135f
	b 2136f
2135:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2136:
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
	cbz x3, 2137f
	b 2138f
2137:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2138:
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
	cbz x3, 2139f
	b 2140f
2139:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2140:
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
	cbz x3, 2141f
	b 2142f
2141:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2142:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2126b
2125:
	ldr x3, [x0, #160]
	cbnz x3, 2143f
	b 2144f
2143:
2145:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2145b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2146f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2148:
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
2149:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2149b
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
	cbnz x4, 2148b
	b 2147f
2146:
	cbz x4, 2150f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2152:
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
2153:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2153b
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
	cbnz x4, 2152b
	b 2151f
2150:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2154:
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
2155:
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
	cbnz x14, 2155b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2154b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2151:
2147:
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
2156:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2156b
	add x13, x12, #0
2157:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2158:
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
	cbnz x14, 2158b
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
2159:
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
	cbnz x14, 2159b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2157b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2160:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2161:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2161b
2144:
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
2162:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	add x13, x12, #0
2163:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2164:
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
	cbnz x14, 2164b
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
2165:
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
	cbnz x14, 2165b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2163b
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
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2168:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2168b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	movz x9, #0, lsl #0
	add x14, x12, #0
2169:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2169b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x9, x8
	csel x9, x7, x8, hs
	add x0, x9, #0
	b 266f
265:
	movz x0, #0, lsl #0
266:
	b 234f
233:
	movz x0, #0, lsl #0
234:
	b 225f
224:
	movz x0, #1, lsl #0
225:
	b 223f
222:
	movz x0, #0, lsl #0
223:
	b 29f
28:
	movz x0, #0, lsl #0
29:
	b 27f
26:
	movz x0, #1, lsl #0
27:
	ret
	.p2align 6

vg_ffdh_exchange:
	ldr x8, [sp, #8]
	str x0, [x8, #176]
	str x2, [x8, #128]
	str x3, [x8, #136]
	str x4, [x8, #144]
	str x5, [x8, #160]
	str x6, [x8, #168]
	str x7, [x8, #152]
	add x0, x8, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
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
	cbz x3, 27f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
29:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 29b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
210:
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
	cbnz x13, 210b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
211:
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
212:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 212b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
213:
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
	cbnz x14, 213b
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
214:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 214b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
215:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 215b
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
216:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 216b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
217:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 217b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 211b
	b 28f
27:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 218f
220:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 220b
	b 219f
218:
219:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
221:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 221b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
222:
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
223:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
225:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 225b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 222b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
226:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 226b
28:
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
227:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 227b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
228:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 229f
	b 230f
229:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
230:
	cbnz x2, 228b
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
231:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 231b
	add x13, x12, #0
232:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
233:
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
	cbnz x14, 233b
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
234:
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
	cbnz x14, 234b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 232b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
235:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 235b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
236:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 237b
	add x13, x12, #0
238:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
239:
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
	cbnz x14, 239b
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
240:
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
	cbnz x14, 240b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 238b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
241:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 241b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
242:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 242b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
243:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 243b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
244:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x5, [x0, #128]
	ldr x3, [x5, #160]
	str x3, [x0, #136]
	ldr x3, [x5, #168]
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
245:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 245b
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
246:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 246b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
247:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 247b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
248:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
	add x13, x12, #0
250:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
251:
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
	cbnz x14, 251b
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
252:
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
	cbnz x14, 252b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 250b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
254:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 254b
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
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 248b
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
	cbnz x9, 256f
	b 257f
256:
258:
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
	cbnz x9, 258b
257:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 259f
	b 260f
259:
261:
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
	cbz x3, 262f
	b 263f
262:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
263:
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
	cbz x3, 264f
	b 265f
264:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
265:
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
	cbz x3, 266f
	b 267f
266:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
267:
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
	cbz x3, 268f
	b 269f
268:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
269:
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
	cbz x3, 270f
	b 271f
270:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
271:
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
	cbz x3, 272f
	b 273f
272:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
273:
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
	cbz x3, 274f
	b 275f
274:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
275:
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
	cbz x3, 276f
	b 277f
276:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
277:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 261b
260:
	ldr x3, [x0, #160]
	cbnz x3, 278f
	b 279f
278:
280:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 280b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 281f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
283:
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
284:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 284b
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
	cbnz x4, 283b
	b 282f
281:
	cbz x4, 285f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
287:
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
288:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 288b
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
	cbnz x4, 287b
	b 286f
285:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
289:
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
290:
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
	cbnz x14, 290b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 289b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
286:
282:
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
291:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 291b
	add x13, x12, #0
292:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
293:
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
	cbnz x14, 293b
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
294:
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
	cbnz x14, 294b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 292b
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
279:
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
297:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 297b
	add x13, x12, #0
298:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
299:
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
	cbnz x14, 299b
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
2100:
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
	cbnz x14, 2100b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 298b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2101:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2102:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2103:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2104:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #88]
	add x14, x12, #0
2105:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2106:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x8, [x0, #112]
	ldr x5, [x0, #128]
	ldr x1, [x5, #176]
	ldr x9, [x5, #144]
	add x1, x1, x9
	movz x7, #0, lsl #0
	ldr x3, [x0, #240]
	sub x15, x7, x3
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2107:
	and x5, x2, x6
	cbz x5, 2108f
	b 2109f
2108:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2109:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2107b
	ldr x0, [x0, #240]
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_check_private:
	str x0, [x7, #128]
	str x1, [x7, #136]
	str x2, [x7, #144]
	str x3, [x7, #152]
	str x5, [x7, #160]
	str x6, [x7, #168]
	add x0, x7, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
27:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 27b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x2, [x5, #168]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
28:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 29f
	b 210f
29:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
210:
	cbnz x2, 28b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #120]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 211b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x8, x7, hs
	str x9, [x0, #240]
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 212f
	ldr x0, [x0, #232]
	ldr x8, [x0, #112]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #144]
	ldr x8, [x0, #112]
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
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
218:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	b 213f
212:
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
219:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
220:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 220b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
213:
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 221f
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
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
	ldr x16, [x0, #120]
	ldr x17, [x0, #104]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 227b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
228:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 229b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 230f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 232f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
234:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 234b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
235:
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
	cbnz x13, 235b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
236:
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
237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 237b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
238:
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
	cbnz x14, 238b
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
239:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 239b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
240:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 240b
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
	cbnz x13, 236b
	b 233f
232:
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
233:
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 252f
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
254:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 254b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	ldr x0, [x0, #232]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
255:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 255b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
256:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 257f
	b 258f
257:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
258:
	cbnz x2, 256b
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
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	add x13, x12, #0
260:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
262:
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
	cbnz x14, 262b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 260b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
263:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 263b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
264:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	add x13, x12, #0
266:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
267:
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
	cbnz x14, 267b
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
268:
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
	cbnz x14, 268b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 266b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
270:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 270b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
271:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
272:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x5, [x0, #128]
	ldr x3, [x5, #184]
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
273:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 273b
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
274:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 274b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
275:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 275b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
276:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 277b
	add x13, x12, #0
278:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
279:
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
	cbnz x14, 279b
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
280:
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
	cbnz x14, 280b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 278b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
281:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 281b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
282:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 282b
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
283:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 276b
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
	cbnz x9, 284f
	b 285f
284:
286:
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
	cbnz x9, 286b
285:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 287f
	b 288f
287:
289:
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
	cbz x3, 290f
	b 291f
290:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
291:
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
	cbz x3, 292f
	b 293f
292:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
293:
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
	cbz x3, 294f
	b 295f
294:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
295:
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
	cbz x3, 296f
	b 297f
296:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
297:
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
	cbz x3, 298f
	b 299f
298:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
299:
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
	cbz x3, 2100f
	b 2101f
2100:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2101:
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
	cbz x3, 2102f
	b 2103f
2102:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2103:
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
	cbz x3, 2104f
	b 2105f
2104:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2105:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 289b
288:
	ldr x3, [x0, #160]
	cbnz x3, 2106f
	b 2107f
2106:
2108:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2108b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2109f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2111:
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
2112:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2112b
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
	cbnz x4, 2111b
	b 2110f
2109:
	cbz x4, 2113f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2115:
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
2116:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2116b
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
	cbnz x4, 2115b
	b 2114f
2113:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2117:
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
2118:
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
	cbnz x14, 2118b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2117b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2114:
2110:
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
2107:
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
2125:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2125b
	add x13, x12, #0
2126:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2127:
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
	cbnz x14, 2127b
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
2128:
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
	cbnz x14, 2128b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2126b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2129:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2130:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2131:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2131b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	movz x9, #0, lsl #0
	add x14, x12, #0
2132:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x9, x8
	csel x9, x7, x8, hs
	b 253f
252:
	ldr x0, [x0, #232]
	movz x9, #1, lsl #0
253:
	cbz x9, 2133f
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2135:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	ldr x5, [x0, #128]
	ldr x1, [x5, #216]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2136:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2137f
	b 2138f
2137:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2138:
	cbnz x2, 2136b
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
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2145:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	add x13, x12, #0
2146:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2147:
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
	cbnz x14, 2147b
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
2148:
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
	cbnz x14, 2148b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2146b
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
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
2151:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
2152:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x5, [x0, #128]
	ldr x3, [x5, #160]
	str x3, [x0, #136]
	ldr x3, [x5, #168]
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
2153:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2153b
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
2154:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2155:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2156:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2157:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2157b
	add x13, x12, #0
2158:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2159:
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
	cbnz x14, 2159b
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
2160:
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
	cbnz x14, 2160b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2158b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2161:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2162:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2162b
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
2163:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2156b
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
	cbnz x9, 2164f
	b 2165f
2164:
2166:
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
	cbnz x9, 2166b
2165:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2167f
	b 2168f
2167:
2169:
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
	cbz x3, 2170f
	b 2171f
2170:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2171:
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
	cbz x3, 2172f
	b 2173f
2172:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2173:
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
	cbz x3, 2174f
	b 2175f
2174:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2175:
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
	cbz x3, 2176f
	b 2177f
2176:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2177:
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
	cbz x3, 2178f
	b 2179f
2178:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2179:
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
	cbz x3, 2180f
	b 2181f
2180:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2181:
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
	cbz x3, 2182f
	b 2183f
2182:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2183:
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
	cbz x3, 2184f
	b 2185f
2184:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2185:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2169b
2168:
	ldr x3, [x0, #160]
	cbnz x3, 2186f
	b 2187f
2186:
2188:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2188b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2189f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2191:
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
2192:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2192b
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
	cbnz x4, 2191b
	b 2190f
2189:
	cbz x4, 2193f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2195:
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
2196:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2196b
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
	cbnz x4, 2195b
	b 2194f
2193:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2197:
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
2198:
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
	cbnz x14, 2198b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2197b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2194:
2190:
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
2199:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2199b
	add x13, x12, #0
2200:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2201:
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
	cbnz x14, 2201b
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
2202:
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
	cbnz x14, 2202b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2200b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2203:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2203b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2204:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2204b
2187:
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
2205:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2205b
	add x13, x12, #0
2206:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2207:
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
	cbnz x14, 2207b
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
2208:
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
	cbnz x14, 2208b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2206b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2209:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2209b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2210:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2210b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2211:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2211b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2212:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2212b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2213:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2214f
	b 2215f
2214:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2215:
	cbnz x2, 2213b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #104]
	movz x9, #0, lsl #0
	add x14, x12, #0
2216:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2216b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x9, x8
	csel x9, x7, x8, hs
	add x0, x9, #0
	b 2134f
2133:
	movz x0, #0, lsl #0
2134:
	b 231f
230:
	movz x0, #0, lsl #0
231:
	b 222f
221:
	movz x0, #2, lsl #0
222:
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_derive_public:
	str x0, [x7, #176]
	str x2, [x7, #128]
	str x3, [x7, #136]
	str x4, [x7, #144]
	str x5, [x7, #160]
	str x6, [x7, #168]
	add x0, x7, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
27:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 27b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x2, [x5, #168]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
28:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 29f
	b 210f
29:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
210:
	cbnz x2, 28b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #120]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 211b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x8, x7, hs
	str x9, [x0, #240]
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 212f
	ldr x0, [x0, #232]
	ldr x8, [x0, #112]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #144]
	ldr x8, [x0, #112]
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
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
218:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	b 213f
212:
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
219:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
220:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 220b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
213:
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 221f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 223f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
225:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
226:
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
	cbnz x13, 226b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
227:
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
228:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 228b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
230:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
231:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 231b
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
232:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 232b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
233:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 233b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 227b
	b 224f
223:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 234f
236:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 236b
	b 235f
234:
235:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 237b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
238:
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
239:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 239b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
240:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
241:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 241b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 238b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
242:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 242b
224:
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
243:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 243b
	ldr x5, [x0, #128]
	ldr x1, [x5, #216]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
244:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 245f
	b 246f
245:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
246:
	cbnz x2, 244b
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
247:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	add x13, x12, #0
248:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
249:
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
	cbnz x14, 249b
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
250:
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
	cbnz x14, 250b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 248b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
251:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 251b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
252:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 252b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
253:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 253b
	add x13, x12, #0
254:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
255:
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
	cbnz x14, 255b
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
256:
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
	cbnz x14, 256b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 254b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
257:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 257b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
258:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
259:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x5, [x0, #128]
	ldr x3, [x5, #160]
	str x3, [x0, #136]
	ldr x3, [x5, #168]
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
261:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 261b
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
262:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 262b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
263:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 263b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
264:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	add x13, x12, #0
266:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
267:
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
	cbnz x14, 267b
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
268:
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
	cbnz x14, 268b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 266b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
270:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 264b
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
	cbnz x9, 272f
	b 273f
272:
274:
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
	cbnz x9, 274b
273:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 275f
	b 276f
275:
277:
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
	cbz x3, 278f
	b 279f
278:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
279:
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
	cbz x3, 280f
	b 281f
280:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
281:
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
	cbz x3, 282f
	b 283f
282:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
283:
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
	cbz x3, 284f
	b 285f
284:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
285:
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
	cbz x3, 286f
	b 287f
286:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
287:
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
	cbz x3, 288f
	b 289f
288:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
289:
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
	cbz x3, 290f
	b 291f
290:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
291:
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
	cbz x3, 292f
	b 293f
292:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
293:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 277b
276:
	ldr x3, [x0, #160]
	cbnz x3, 294f
	b 295f
294:
296:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 296b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 297f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
299:
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
2100:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
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
	cbnz x4, 299b
	b 298f
297:
	cbz x4, 2101f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2103:
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
2104:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2104b
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
	cbnz x4, 2103b
	b 2102f
2101:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2105:
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
2106:
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
	cbnz x14, 2106b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2105b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2102:
298:
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
2107:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	add x13, x12, #0
2108:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2109:
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
	cbnz x14, 2109b
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
2110:
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
	cbnz x14, 2110b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2108b
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
295:
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
2113:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	add x13, x12, #0
2114:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2115:
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
	cbnz x14, 2115b
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
2116:
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
	cbnz x14, 2116b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2114b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2117:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2118:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2119:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2120:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #88]
	add x14, x12, #0
2121:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2122:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x8, [x0, #112]
	ldr x5, [x0, #128]
	ldr x1, [x5, #176]
	ldr x9, [x5, #144]
	add x1, x1, x9
	movz x7, #0, lsl #0
	ldr x3, [x0, #240]
	sub x15, x7, x3
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2123:
	and x5, x2, x6
	cbz x5, 2124f
	b 2125f
2124:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2125:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2123b
	ldr x9, [x0, #240]
	movz x0, #3, lsl #0
	lsl x9, x9, #1
	sub x0, x0, x9
	b 222f
221:
	ldr x0, [x0, #128]
	ldr x1, [x0, #176]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2126:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2126b
	movz x0, #2, lsl #0
222:
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_generate_key:
	ldr x8, [sp, #8]
	str x0, [x8, #160]
	str x2, [x8, #152]
	str x4, [x8, #128]
	str x5, [x8, #136]
	str x6, [x8, #144]
	str x7, [x8, #200]
	add x0, x8, #0
	ldr x2, [x0, #128]
	ldr x3, [x0, #144]
	add x4, x2, x3
	str x4, [x0, #216]
	add x4, x4, x3
	str x4, [x0, #224]
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
	add x5, x0, #0
	ldr x4, [x5, #120]
	ldr x6, [x5, #48]
	add x6, x6, #2
	lsl x6, x6, #3
	add x4, x4, x6
	str x4, [x0, #232]
	ldr x12, [x0, #144]
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #144]
	ldr x8, [x0, #64]
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
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 27f
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
29:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 29b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	b 28f
27:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
210:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 210b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
28:
	lsr x5, x3, #1
	orr x3, x3, x5
	lsr x5, x3, #2
	orr x3, x3, x5
	lsr x5, x3, #4
	orr x3, x3, x5
	add x12, x3, #0
	ldr x10, [x0, #144]
	ldr x11, [x0, #192]
	sub x11, x10, x11
	ldr x2, [x0, #160]
	ldr x1, [x0, #200]
	movz x13, #255, lsl #0
	movz x7, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x14, [x0, #144]
211:
	ldrb w4, [x1, #0]
	subs x5, x10, x11
	csel x6, x13, x7, hs
	eor x5, x10, x11
	movz x8, #1, lsl #0
	subs x5, x5, x8
	csel x6, x6, x12, hs
	and x4, x4, x6
	strb w4, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	add x10, x10, #1
	sub x14, x14, #1
	cbnz x14, 211b
	ldr x0, [x0, #232]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
212:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 212b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
213:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 214f
	b 215f
214:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
215:
	cbnz x2, 213b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #120]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
216:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 216b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x8, x7, hs
	str x9, [x0, #240]
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 217f
	ldr x0, [x0, #232]
	ldr x8, [x0, #112]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x5, [x0, #128]
	ldr x1, [x5, #224]
	ldr x2, [x5, #144]
	ldr x8, [x0, #112]
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
	ldr x16, [x0, #104]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
223:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 223b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	b 218f
217:
	ldr x0, [x0, #232]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #88]
	add x14, x12, #0
224:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 224b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
225:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 225b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
218:
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	cbz x9, 226f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 228f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
230:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 230b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
231:
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
	cbnz x13, 231b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
232:
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
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
236:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 236b
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
237:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
238:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 232b
	b 229f
228:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 239f
241:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 241b
	b 240f
239:
240:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
242:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 242b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
243:
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
244:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
245:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
246:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 246b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 243b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
247:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 247b
229:
	ldr x0, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 248f
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
250:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 250b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	b 249f
248:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
251:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 251b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
249:
	ldr x10, [x0, #144]
	ldr x11, [x0, #192]
	sub x11, x10, x11
	ldr x2, [x0, #160]
	add x3, x2, x11
	str x3, [x0, #184]
	ldr x0, [x0, #232]
	ldr x8, [x0, #104]
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
	ldr x1, [x5, #216]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
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
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	add x13, x12, #0
257:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
258:
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
	cbnz x14, 258b
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
259:
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
	cbnz x14, 259b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 257b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
260:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 260b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
261:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 261b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
262:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 262b
	add x13, x12, #0
263:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
264:
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
	cbnz x14, 264b
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
265:
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
	cbnz x14, 265b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 263b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
266:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
268:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
269:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x5, [x0, #128]
	ldr x3, [x5, #184]
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
270:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
272:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 272b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
273:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
274:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 274b
	add x13, x12, #0
275:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
276:
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
	cbnz x14, 276b
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
277:
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
	cbnz x14, 277b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 275b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
278:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
279:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 279b
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
280:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 280b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 273b
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
	cbnz x9, 281f
	b 282f
281:
283:
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
	cbnz x9, 283b
282:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 284f
	b 285f
284:
286:
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
	cbz x3, 287f
	b 288f
287:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
288:
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
	cbz x3, 289f
	b 290f
289:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
290:
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
	cbz x3, 291f
	b 292f
291:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
292:
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
	cbz x3, 293f
	b 294f
293:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
294:
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
	cbz x3, 295f
	b 296f
295:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
296:
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
	cbz x3, 297f
	b 298f
297:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
298:
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
	cbz x3, 299f
	b 2100f
299:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2100:
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
	cbz x3, 2101f
	b 2102f
2101:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2102:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 286b
285:
	ldr x3, [x0, #160]
	cbnz x3, 2103f
	b 2104f
2103:
2105:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2105b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2106f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2108:
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
2109:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2109b
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
	cbnz x4, 2108b
	b 2107f
2106:
	cbz x4, 2110f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2112:
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
2113:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
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
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #32
	cbnz x4, 2112b
	b 2111f
2110:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2114:
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
2115:
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
	cbnz x14, 2115b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2114b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2111:
2107:
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
2116:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	add x13, x12, #0
2117:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2118:
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
	cbnz x14, 2118b
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
2119:
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
	cbnz x14, 2119b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2117b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2120:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2121:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2121b
2104:
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
2122:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	add x13, x12, #0
2123:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2124:
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
	cbnz x14, 2124b
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
2125:
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
	cbnz x14, 2125b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2123b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2126:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2126b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2127:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2128:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2128b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2129:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #88]
	add x14, x12, #0
2130:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	ldr x16, [x0, #88]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #88]
	ldr x17, [x0, #64]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
2131:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2131b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	csel x9, x7, x8, hs
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	ldr x12, [x0, #48]
	ldr x8, [x0, #112]
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x9, [x5, #144]
	add x1, x1, x9
	movz x7, #0, lsl #0
	sub x15, x7, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2132:
	and x5, x2, x6
	cbz x5, 2133f
	b 2134f
2133:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2134:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2132b
	ldr x9, [x0, #240]
	ldr x0, [x0, #128]
	str x9, [x0, #240]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	sub x3, x3, x4
	sub x3, x3, x4
	cbz x3, 2135f
	ldr x1, [x0, #224]
	ldr x2, [x0, #144]
2137:
	ldrb w4, [x1, #0]
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x4, x8
	csel x5, x7, x8, hs
	movz x9, #2, lsl #0
	subs x3, x2, x9
	csel x6, x8, x7, hs
	and x5, x5, x6
	add x1, x1, x5
	sub x2, x2, x5
	cbnz x5, 2137b
	str x1, [x0, #184]
	str x2, [x0, #192]
	ldrb w3, [x1, #0]
	ldr x0, [x0, #232]
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2138:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	ldr x5, [x0, #128]
	ldr x1, [x5, #152]
	ldr x2, [x5, #144]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2139:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2140f
	b 2141f
2140:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2141:
	cbnz x2, 2139b
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
2142:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	add x13, x12, #0
2143:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2144:
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
	cbnz x14, 2144b
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
2145:
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
	cbnz x14, 2145b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2143b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2146:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2146b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2147:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2148:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	add x13, x12, #0
2149:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2150:
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
	cbnz x14, 2150b
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
2151:
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
	cbnz x14, 2151b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2149b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2152:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2153:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #72]
	add x14, x12, #0
2154:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
2155:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	ldr x5, [x0, #128]
	ldr x3, [x5, #184]
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
2156:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2156b
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
2157:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2157b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2158:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	movz x3, #30, lsl #0
	str x3, [x0, #160]
2159:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2160:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	add x13, x12, #0
2161:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2162:
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
	cbnz x14, 2162b
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
2163:
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
	cbnz x14, 2163b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2161b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2164:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2164b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2165:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2165b
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
2166:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2159b
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
	cbnz x9, 2167f
	b 2168f
2167:
2169:
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
	cbnz x9, 2169b
2168:
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2170f
	b 2171f
2170:
2172:
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
	cbz x3, 2173f
	b 2174f
2173:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2174:
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
	cbz x3, 2175f
	b 2176f
2175:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2176:
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
	cbz x3, 2177f
	b 2178f
2177:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2178:
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
	cbz x3, 2179f
	b 2180f
2179:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2180:
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
	cbz x3, 2181f
	b 2182f
2181:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2182:
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
	cbz x3, 2183f
	b 2184f
2183:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2184:
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
	cbz x3, 2185f
	b 2186f
2185:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2186:
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
	cbz x3, 2187f
	b 2188f
2187:
	mov v7.d[0], x30
	bl {vg_rsa_square_window5}
	umov x30, v7.d[0]
2188:
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x3, [x0, #144]
	ldr x4, [x0, #152]
	sub x3, x3, x4
	cbnz x3, 2172b
2171:
	ldr x3, [x0, #160]
	cbnz x3, 2189f
	b 2190f
2189:
2191:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2191b
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 2192f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2194:
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
2195:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2195b
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
	cbnz x4, 2194b
	b 2193f
2192:
	cbz x4, 2196f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2198:
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
2199:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2199b
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
	cbnz x4, 2198b
	b 2197f
2196:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
2200:
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
2201:
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
	cbnz x14, 2201b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 2200b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
2197:
2193:
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
2202:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2202b
	add x13, x12, #0
2203:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2204:
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
	cbnz x14, 2204b
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
2205:
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
	cbnz x14, 2205b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2203b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2206:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2206b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2207:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2207b
2190:
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
2208:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2208b
	add x13, x12, #0
2209:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2210:
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
	cbnz x14, 2210b
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
2211:
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
	cbnz x14, 2211b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2209b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2212:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2212b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2213:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2213b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2214:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2214b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	movz x9, #0, lsl #0
	add x14, x12, #0
2215:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2215b
	movz x7, #0, lsl #0
	movz x8, #1, lsl #0
	subs x3, x9, x8
	csel x9, x7, x8, hs
	ldr x0, [x0, #128]
	ldr x3, [x0, #240]
	and x9, x9, x3
	str x9, [x0, #240]
	b 2136f
2135:
2136:
	ldr x9, [x0, #240]
	movz x7, #0, lsl #0
	sub x15, x7, x9
	ldr x1, [x0, #160]
	ldr x2, [x0, #144]
2216:
	ldrb w4, [x1, #0]
	and x4, x4, x15
	strb w4, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2216b
	ldr x1, [x0, #152]
	ldr x2, [x0, #144]
2217:
	ldrb w4, [x1, #0]
	and x4, x4, x15
	strb w4, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2217b
	ldr x9, [x0, #240]
	movz x0, #3, lsl #0
	lsl x9, x9, #1
	sub x0, x0, x9
	b 227f
226:
	ldr x0, [x0, #128]
	ldr x1, [x0, #160]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2218:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2218b
	ldr x1, [x0, #152]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2219:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2219b
	movz x0, #2, lsl #0
227:
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_parameter_generation_init:
	movz x11, #0, lsl #0
	movz x12, #1, lsl #0
	movz x9, #512, lsl #0
	subs x10, x1, x9
	csel x13, x12, x11, hs
	movz x9, #8193, lsl #0
	subs x10, x1, x9
	csel x14, x11, x12, hs
	and x13, x13, x14
	add w2, w2, #0
	movz x9, #2, lsl #0
	subs x10, x2, x9
	csel x15, x12, x11, hs
	movz x9, #3, lsl #0
	subs x10, x2, x9
	csel x16, x11, x12, hs
	and x15, x15, x16
	movz x9, #5, lsl #0
	subs x10, x2, x9
	csel x16, x12, x11, hs
	movz x9, #6, lsl #0
	subs x10, x2, x9
	csel x17, x11, x12, hs
	and x16, x16, x17
	orr x15, x15, x16
	and x13, x13, x15
	cbz x13, 20f
	mul x9, x1, x1
	lsl x9, x9, #6
	add x10, x1, #7
	lsr x10, x10, #3
	lsl x11, x10, #15
	add x11, x11, x10
	lsl x12, x10, #9
	str x9, [x0, #0]
	str x10, [x0, #8]
	str x11, [x0, #16]
	str x12, [x0, #24]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_key_generation_init:
	movz x9, #64, lsl #0
	movz x11, #0, lsl #0
	movz x12, #1, lsl #0
	subs x10, x1, x9
	csel x13, x12, x11, hs
	movz x9, #1025, lsl #0
	subs x10, x1, x9
	csel x14, x11, x12, hs
	and x13, x13, x14
	cbz x13, 20f
	movz x9, #128, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x1, [x0, #16]
	str x1, [x0, #24]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	movz x0, #0, lsl #0
21:
	ret
	.p2align 6

vg_ffdh_generate_key_search:
	add x14, sp, #0
	ldr x8, [x14, #32]
	ldr x9, [x14, #0]
	ldr x10, [x14, #8]
	ldr x11, [x14, #16]
	ldr x12, [x14, #24]
	str x19, [x8, #32]
	add x19, x8, #0
	movz x13, #0, lsl #0
	str x0, [x19, #40]
	str x2, [x19, #48]
	str x5, [x19, #56]
	str x6, [x19, #64]
	str x9, [x19, #72]
	str x10, [x19, #80]
	str x13, [x19, #88]
	str x11, [x19, #96]
	str x12, [x19, #104]
	str x4, [x19, #120]
	str x30, [sp, #-16]!
20:
	ldr x9, [x19, #0]
	cbz x9, 21f
	ldr x9, [x19, #8]
	cbz x9, 23f
	ldr x9, [x19, #80]
	ldr x10, [x19, #16]
	movz x13, #0, lsl #0
	movz x14, #1, lsl #0
	subs x11, x9, x10
	csel x12, x14, x13, hs
	cbz x12, 25f
	sub sp, sp, #32
	ldr x0, [x19, #40]
	ldr x1, [x19, #16]
	ldr x2, [x19, #48]
	ldr x3, [x19, #16]
	ldr x4, [x19, #56]
	ldr x5, [x19, #64]
	ldr x6, [x19, #16]
	ldr x7, [x19, #72]
	ldr x9, [x19, #96]
	ldr x10, [x19, #104]
	add x11, sp, #0
	str x1, [x11, #0]
	str x9, [x11, #8]
	str x10, [x11, #16]
	bl {vg_ffdh_generate_key}
	add sp, sp, #32
	add w9, w0, #0
	ldr x11, [x19, #16]
	ldr x12, [x19, #72]
	ldr x13, [x19, #80]
	ldr x14, [x19, #88]
	add x12, x12, x11
	sub x13, x13, x11
	add x14, x14, x11
	str x12, [x19, #72]
	str x13, [x19, #80]
	str x14, [x19, #88]
	sub x10, x9, #1
	cbz x10, 27f
	sub x10, x9, #2
	cbz x10, 29f
	sub x10, x9, #3
	cbz x10, 211f
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
213:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 213b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
214:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 214b
	b 212f
211:
	ldr x10, [x19, #0]
	sub x10, x10, #1
	movz x11, #128, lsl #0
	movz x12, #4, lsl #0
	str x10, [x19, #0]
	str x11, [x19, #8]
	str x12, [x19, #112]
212:
	b 210f
29:
	ldr x10, [x19, #8]
	sub x10, x10, #1
	movz x11, #4, lsl #0
	str x10, [x19, #8]
	str x11, [x19, #112]
210:
	b 28f
27:
	movz x10, #0, lsl #0
	movz x11, #1, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
28:
	b 26f
25:
	ldr x10, [x19, #16]
	movz x11, #0, lsl #0
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
215:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 215b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
216:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 216b
26:
	b 24f
23:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
217:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 217b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
218:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 218b
24:
	b 22f
21:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #8]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
219:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 219b
	ldr x1, [x19, #48]
	ldr x2, [x19, #16]
	movz x3, #0, lsl #0
220:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 220b
22:
	ldr x9, [x19, #112]
	sub x9, x9, #4
	cbz x9, 20b
	ldr x30, [sp], #16
	ldr x1, [x19, #120]
	ldr x2, [x19, #88]
	ldr x0, [x19, #112]
	ldr x19, [x19, #32]
	str x2, [x1, #0]
	ret
	.p2align 6

vg_ffdh_generate_parameters:
	add x14, sp, #0
	ldr x8, [x14, #8]
	ldr x9, [x14, #0]
	add w4, w4, #0
	str x19, [x8, #32]
	add x19, x8, #0
	movz x13, #0, lsl #0
	str x0, [x19, #40]
	str x1, [x19, #48]
	str x2, [x19, #56]
	str x3, [x19, #64]
	str x4, [x19, #72]
	str x5, [x19, #80]
	str x6, [x19, #88]
	str x13, [x19, #96]
	str x7, [x19, #104]
	str x9, [x19, #120]
	str x30, [sp, #-16]!
20:
	ldr x9, [x19, #0]
	cbz x9, 21f
	sub sp, sp, #16
	ldr x0, [x19, #40]
	ldr x1, [x19, #48]
	ldr x2, [x19, #56]
	ldr x3, [x19, #64]
	ldr x4, [x19, #72]
	ldr x5, [x19, #80]
	ldr x6, [x19, #88]
	ldr x7, [x19, #104]
	ldr x9, [x19, #120]
	add x11, sp, #0
	str x9, [x11, #0]
	bl {vg_ffdh_parameter_candidate}
	add sp, sp, #16
	add w9, w0, #0
	ldr x11, [x19, #56]
	ldr x10, [x11, #0]
	sub x12, x9, #1
	cbz x12, 23f
	sub x12, x9, #2
	cbz x12, 25f
	ldr x10, [x19, #88]
	ldr x11, [x19, #16]
	subs x12, x10, x11
	movz x13, #0, lsl #0
	movz x14, #1, lsl #0
	csel x12, x14, x13, hs
	cbz x12, 27f
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #48]
	movz x3, #0, lsl #0
29:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 29b
	b 28f
27:
	ldr x10, [x19, #88]
	ldr x11, [x19, #48]
	ldr x12, [x19, #16]
	lsl x11, x11, #8
	subs x13, x10, x11
	csel x10, x10, x11, hs
	add x10, x10, x10
	subs x13, x10, x12
	csel x10, x12, x10, hs
	movz x11, #0, lsl #0
	str x10, [x19, #24]
	str x11, [x19, #112]
28:
	b 26f
25:
	ldr x11, [x19, #96]
	ldr x12, [x19, #80]
	ldr x13, [x19, #88]
	ldr x14, [x19, #0]
	add x11, x11, x10
	add x12, x12, x10
	sub x13, x13, x10
	sub x14, x14, #1
	movz x15, #4, lsl #0
	str x11, [x19, #96]
	str x12, [x19, #80]
	str x13, [x19, #88]
	str x14, [x19, #0]
	str x15, [x19, #112]
26:
	b 24f
23:
	ldr x11, [x19, #96]
	add x11, x11, x10
	str x11, [x19, #96]
	movz x10, #0, lsl #0
	movz x11, #1, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #112]
24:
	b 22f
21:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #112]
	ldr x1, [x19, #40]
	ldr x2, [x19, #48]
	movz x3, #0, lsl #0
210:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 210b
22:
	ldr x9, [x19, #112]
	sub x9, x9, #4
	cbz x9, 20b
	ldr x30, [sp], #16
	ldr x1, [x19, #56]
	ldr x2, [x19, #96]
	ldr x0, [x19, #112]
	ldr x19, [x19, #32]
	str x2, [x1, #0]
	ret
	.p2align 6
