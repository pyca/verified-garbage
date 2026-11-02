// The functions of `src/rsa.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_square_4_4:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 22f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
24:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 24b
	add x13, x12, #0
25:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
26:
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
	cbnz x14, 26b
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
27:
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
	cbnz x14, 27b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 25b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
28:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 28b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
29:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 29b
	b 23f
22:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
211:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 212f
	b 213f
212:
214:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 214b
213:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 215f
	b 216f
215:
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
216:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 211b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
218:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 218b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
219:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 220f
	b 221f
220:
222:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 222b
221:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 223f
	b 224f
223:
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
224:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 219b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #96]
	ldr x6, [x0, #80]
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
23:
	b 21f
20:
	cbz x4, 228f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 230f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
232:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 232b
	add x13, x12, #0
233:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
235:
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
	cbnz x14, 235b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 233b
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
	b 231f
230:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
238:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 238b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
239:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 240f
	b 241f
240:
242:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 242b
241:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 243f
	b 244f
243:
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
244:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 239b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
246:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 246b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
247:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 248f
	b 249f
248:
250:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 250b
249:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 251f
	b 252f
251:
253:
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
	cbnz x14, 253b
252:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 247b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #96]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
254:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 255b
231:
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
	add x14, x14, #2
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
257:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 258f
	b 259f
258:
260:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 260b
259:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 261f
	b 262f
261:
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
262:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 257b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
264:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 264b
	str x5, [x16, #0]
	ldr x16, [x0, #96]
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
265:
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
266:
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
	cbnz x15, 266b
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
	cbnz x12, 265b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #96]
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
	ldr x5, [x0, #96]
	ldr x6, [x0, #80]
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
229:
21:
	ret
	.p2align 6

vg_rsa_square_6_6:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 22f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 24f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
26:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	add x13, x12, #0
27:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
28:
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
	cbnz x14, 28b
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
29:
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
	cbnz x14, 29b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 27b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
210:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 210b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
211:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 211b
	b 25f
24:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
212:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 212b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
213:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 214f
	b 215f
214:
216:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 216b
215:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 217f
	b 218f
217:
219:
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
	cbnz x14, 219b
218:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 213b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
220:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 220b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
221:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 222f
	b 223f
222:
224:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 224b
223:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 225f
	b 226f
225:
227:
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
	cbnz x14, 227b
226:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 221b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
229:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 229b
25:
	b 23f
22:
	cbz x4, 230f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 232f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
234:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	add x13, x12, #0
235:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
237:
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
	cbnz x14, 237b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 235b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
238:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
239:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 239b
	b 233f
232:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
241:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 242f
	b 243f
242:
244:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 244b
243:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 245f
	b 246f
245:
247:
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
	cbnz x14, 247b
246:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 241b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
248:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 248b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
249:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 250f
	b 251f
250:
252:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 252b
251:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 253f
	b 254f
253:
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
254:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 249b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
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
233:
	b 231f
230:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
258:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 258b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
259:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 260f
	b 261f
260:
262:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 262b
261:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 263f
	b 264f
263:
265:
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
	cbnz x14, 265b
264:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 259b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
266:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 266b
	str x5, [x16, #0]
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
267:
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
268:
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
	cbnz x15, 268b
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
	cbnz x12, 267b
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
231:
23:
	b 21f
20:
	cbz x4, 271f
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 273f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 275f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #112]
	ldr x5, [x0, #112]
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
	b 276f
275:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 283b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
284:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 285f
	b 286f
285:
287:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 287b
286:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 288f
	b 289f
288:
290:
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
	cbnz x14, 290b
289:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 284b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
291:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 291b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
292:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 293f
	b 294f
293:
295:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 295b
294:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 296f
	b 297f
296:
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
297:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 292b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
299:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2100b
276:
	b 274f
273:
	cbz x4, 2101f
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	cbnz x3, 2103f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
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
	add x14, x14, #2
2111:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
2112:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 2113f
	b 2114f
2113:
2115:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 2115b
2114:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 2116f
	b 2117f
2116:
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
2117:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 2112b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
2119:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	str x5, [x16, #0]
	add x13, x12, #0
	movz x5, #0, lsl #0
2120:
	ldr x3, [x8, #0]
	mul x1, x3, x15
	add x16, x8, #0
	add x17, x10, #0
	adds x2, x7, x7
	lsr x14, x12, #2
	cbnz x14, 2121f
	b 2122f
2121:
2123:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 2123b
2122:
	movz x3, #3, lsl #0
	and x14, x12, x3
	cbnz x14, 2124f
	b 2125f
2124:
2126:
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
	cbnz x14, 2126b
2125:
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	adc x6, x7, x7
	adds x3, x3, x5
	adc x5, x6, x7
	str x3, [x16, #0]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2120b
	add x16, x16, #8
	str x5, [x16, #0]
	str x7, [x16, #8]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2127:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2128:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2128b
2104:
	b 2102f
2101:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	add x14, x14, #2
2129:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	add x5, x8, #8
	add x11, x9, #8
	movz x13, #1, lsl #0
	sub x6, x12, #1
2130:
	ldr x1, [x11, #0]
	add x16, x5, #0
	add x17, x9, #0
	adds x2, x7, x7
	lsr x14, x13, #2
	cbnz x14, 2131f
	b 2132f
2131:
2133:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	ldr x3, [x17, #8]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #8]
	ldr x3, [x17, #16]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #16]
	adds x4, x4, x3
	str x4, [x16, #16]
	ldr x3, [x17, #24]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #24]
	adds x4, x4, x3
	str x4, [x16, #24]
	add x16, x16, #32
	add x17, x17, #32
	sub x14, x14, #1
	cbnz x14, 2133b
2132:
	movz x3, #3, lsl #0
	and x14, x13, x3
	cbnz x14, 2134f
	b 2135f
2134:
2136:
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
	cbnz x14, 2136b
2135:
	adc x2, x2, x7
	str x2, [x16, #0]
	add x5, x5, #8
	add x11, x11, #8
	add x13, x13, #1
	sub x6, x6, #1
	cbnz x6, 2130b
	add x16, x8, #0
	add x11, x9, #0
	add x14, x12, #0
	movz x5, #0, lsl #0
2137:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	adds x3, x3, x3
	adcs x4, x4, x4
	adc x6, x7, x7
	adds x3, x3, x2
	adcs x4, x4, x1
	adc x6, x6, x7
	adds x3, x3, x5
	adcs x4, x4, x7
	adc x5, x6, x7
	str x3, [x16, #0]
	str x4, [x16, #8]
	add x16, x16, #16
	add x11, x11, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	str x5, [x16, #0]
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
2138:
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
2139:
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
	cbnz x15, 2139b
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
	cbnz x12, 2138b
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
	add x14, x12, #0
	subs x3, x7, x7
2140:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2141:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2141b
2102:
274:
	b 272f
271:
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
2142:
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
	cbnz x14, 2142b
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
2143:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	lsl x16, x16, #1
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x2, [x8, #0]
	ldr x3, [x8, #8]
	ldr x4, [x8, #16]
	ldr x5, [x8, #24]
	ldr x6, [x8, #32]
	ldr x9, [x8, #40]
	ldr x11, [x8, #48]
	ldr x27, [x8, #56]
	mul x13, x3, x2
	adds x20, x7, x13
	adc x21, x7, x7
	umulh x13, x3, x2
	adds x21, x21, x13
	str x20, [x16, #8]
	mul x13, x4, x2
	adds x21, x21, x13
	mul x13, x4, x3
	adcs x22, x7, x13
	adc x23, x7, x7
	umulh x13, x4, x2
	adds x22, x22, x13
	umulh x13, x4, x3
	adcs x23, x23, x13
	str x21, [x16, #16]
	mul x13, x5, x2
	adds x22, x22, x13
	mul x13, x5, x3
	adcs x23, x23, x13
	mul x13, x5, x4
	adcs x24, x7, x13
	adc x25, x7, x7
	umulh x13, x5, x2
	adds x23, x23, x13
	umulh x13, x5, x3
	adcs x24, x24, x13
	umulh x13, x5, x4
	adcs x25, x25, x13
	str x22, [x16, #24]
	mul x13, x6, x2
	adds x23, x23, x13
	mul x13, x6, x3
	adcs x24, x24, x13
	mul x13, x6, x4
	adcs x25, x25, x13
	mul x13, x6, x5
	adcs x26, x7, x13
	adc x19, x7, x7
	umulh x13, x6, x2
	adds x24, x24, x13
	umulh x13, x6, x3
	adcs x25, x25, x13
	umulh x13, x6, x4
	adcs x26, x26, x13
	umulh x13, x6, x5
	adcs x19, x19, x13
	str x23, [x16, #32]
	mul x13, x9, x2
	adds x24, x24, x13
	mul x13, x9, x3
	adcs x25, x25, x13
	mul x13, x9, x4
	adcs x26, x26, x13
	mul x13, x9, x5
	adcs x19, x19, x13
	mul x13, x9, x6
	adcs x20, x7, x13
	adc x21, x7, x7
	umulh x13, x9, x2
	adds x25, x25, x13
	umulh x13, x9, x3
	adcs x26, x26, x13
	umulh x13, x9, x4
	adcs x19, x19, x13
	umulh x13, x9, x5
	adcs x20, x20, x13
	umulh x13, x9, x6
	adcs x21, x21, x13
	str x24, [x16, #40]
	mul x13, x11, x2
	adds x25, x25, x13
	mul x13, x11, x3
	adcs x26, x26, x13
	mul x13, x11, x4
	adcs x19, x19, x13
	mul x13, x11, x5
	adcs x20, x20, x13
	mul x13, x11, x6
	adcs x21, x21, x13
	mul x13, x11, x9
	adcs x22, x7, x13
	adc x23, x7, x7
	umulh x13, x11, x2
	adds x26, x26, x13
	umulh x13, x11, x3
	adcs x19, x19, x13
	umulh x13, x11, x4
	adcs x20, x20, x13
	umulh x13, x11, x5
	adcs x21, x21, x13
	umulh x13, x11, x6
	adcs x22, x22, x13
	umulh x13, x11, x9
	adcs x23, x23, x13
	str x25, [x16, #48]
	mul x13, x27, x2
	adds x26, x26, x13
	mul x13, x27, x3
	adcs x19, x19, x13
	mul x13, x27, x4
	adcs x20, x20, x13
	mul x13, x27, x5
	adcs x21, x21, x13
	mul x13, x27, x6
	adcs x22, x22, x13
	mul x13, x27, x9
	adcs x23, x23, x13
	mul x13, x27, x11
	adcs x24, x7, x13
	adc x25, x7, x7
	umulh x13, x27, x2
	adds x19, x19, x13
	umulh x13, x27, x3
	adcs x20, x20, x13
	umulh x13, x27, x4
	adcs x21, x21, x13
	umulh x13, x27, x5
	adcs x22, x22, x13
	umulh x13, x27, x6
	adcs x23, x23, x13
	umulh x13, x27, x9
	adcs x24, x24, x13
	umulh x13, x27, x11
	adcs x25, x25, x13
	str x26, [x16, #56]
	str x19, [x16, #64]
	str x20, [x16, #72]
	str x21, [x16, #80]
	str x22, [x16, #88]
	str x23, [x16, #96]
	str x24, [x16, #104]
	str x25, [x16, #112]
	movz x10, #0, lsl #0
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, x12
	cbnz x15, 2144f
	b 2145f
2144:
2146:
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
	cbnz x15, 2146b
2145:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	lsl x16, x16, #1
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x13, [x16, #64]
	adds x13, x13, x10
	str x13, [x16, #64]
	ldr x13, [x16, #72]
	adcs x13, x13, x7
	str x13, [x16, #72]
	ldr x13, [x16, #80]
	adcs x13, x13, x7
	str x13, [x16, #80]
	ldr x13, [x16, #88]
	adcs x13, x13, x7
	str x13, [x16, #88]
	ldr x13, [x16, #96]
	adcs x13, x13, x7
	str x13, [x16, #96]
	ldr x13, [x16, #104]
	adcs x13, x13, x7
	str x13, [x16, #104]
	ldr x13, [x16, #112]
	adcs x13, x13, x7
	str x13, [x16, #112]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 2143b
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
	add x16, x8, #0
	add x11, x9, #0
	lsr x14, x12, #2
	adds x5, x7, x7
2147:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #0]
	str x6, [x16, #8]
	ldr x1, [x11, #8]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #16]
	ldr x4, [x16, #24]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #16]
	str x6, [x16, #24]
	ldr x1, [x11, #16]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #32]
	ldr x4, [x16, #40]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #32]
	str x6, [x16, #40]
	ldr x1, [x11, #24]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #48]
	ldr x4, [x16, #56]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #48]
	str x6, [x16, #56]
	add x16, x16, #64
	add x11, x11, #32
	sub x14, x14, #1
	cbnz x14, 2147b
	lsr x5, x5, #63
	adc x5, x5, x7
	str x5, [x16, #0]
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
2148:
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
2149:
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
	cbnz x15, 2149b
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
	cbnz x12, 2148b
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
2150:
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
	cbnz x14, 2150b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
2151:
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
	cbnz x14, 2151b
272:
21:
	ret
	.p2align 6

vg_rsa_square_window5:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 22f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
24:
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
25:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 25b
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
	cbnz x4, 24b
	b 23f
22:
	cbz x4, 26f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
28:
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
29:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 29b
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
	cbnz x4, 28b
	b 27f
26:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
210:
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
211:
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
	cbnz x14, 211b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 210b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
27:
23:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 212f
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
214:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	add x13, x12, #0
215:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
216:
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
	cbnz x14, 216b
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
217:
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
	cbnz x14, 217b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 215b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
218:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 218b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
219:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 219b
	b 213f
212:
	cbz x4, 220f
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
228:
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
	cbnz x14, 228b
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
229:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
230:
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
	cbnz x15, 230b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 229b
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
231:
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
232:
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
	cbnz x15, 232b
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
	cbnz x12, 231b
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
233:
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
	cbnz x14, 233b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
234:
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
	cbnz x14, 234b
221:
213:
	movz x3, #0, lsl #0
	str x3, [x0, #216]
	str x3, [x0, #160]
	b 21f
20:
	cbz x4, 235f
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
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	lsr x3, x12, #3
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 237f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
239:
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
240:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 240b
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
	cbnz x4, 239b
	b 238f
237:
	cbz x4, 241f
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
243:
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
244:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 244b
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
	cbnz x4, 243b
	b 242f
241:
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
245:
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
246:
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
	cbnz x14, 246b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 245b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
242:
238:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 247f
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
	b 248f
247:
	cbz x4, 255f
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
257:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
	add x13, x12, #0
258:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
259:
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
	cbnz x14, 259b
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
260:
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
	cbnz x14, 260b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 258b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
261:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 261b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
262:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 262b
	b 256f
255:
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
263:
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
	cbnz x14, 263b
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
264:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
265:
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
	cbnz x15, 265b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 264b
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
266:
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
267:
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
	cbnz x15, 267b
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
	cbnz x12, 266b
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
268:
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
	cbnz x14, 268b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
269:
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
	cbnz x14, 269b
256:
248:
	movz x3, #0, lsl #0
	str x3, [x0, #216]
	str x3, [x0, #160]
	b 236f
235:
	mov v0.d[0], x19
	mov v1.d[0], x20
	mov v2.d[0], x21
	mov v3.d[0], x22
	mov v4.d[0], x23
	mov v5.d[0], x24
	mov v6.d[0], x25
	mov v27.d[0], x26
	mov v28.d[0], x27
	mov v29.d[0], x28
	mov v30.d[0], x30
	movz x3, #5, lsl #0
	str x3, [x0, #160]
270:
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x14, x12, #4
	add x16, x8, x14
	str x7, [x16, #0]
	str x7, [x16, #8]
	ldr x8, [x0, #112]
	lsr x12, x12, #3
271:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	lsl x16, x16, #1
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	str x7, [x16, #0]
	str x7, [x16, #120]
	ldr x2, [x8, #0]
	ldr x3, [x8, #8]
	ldr x4, [x8, #16]
	ldr x5, [x8, #24]
	ldr x6, [x8, #32]
	ldr x9, [x8, #40]
	ldr x11, [x8, #48]
	ldr x27, [x8, #56]
	mul x13, x3, x2
	adds x20, x7, x13
	adc x21, x7, x7
	umulh x13, x3, x2
	adds x21, x21, x13
	str x20, [x16, #8]
	mul x13, x4, x2
	adds x21, x21, x13
	mul x13, x4, x3
	adcs x22, x7, x13
	adc x23, x7, x7
	umulh x13, x4, x2
	adds x22, x22, x13
	umulh x13, x4, x3
	adcs x23, x23, x13
	str x21, [x16, #16]
	mul x13, x5, x2
	adds x22, x22, x13
	mul x13, x5, x3
	adcs x23, x23, x13
	mul x13, x5, x4
	adcs x24, x7, x13
	adc x25, x7, x7
	umulh x13, x5, x2
	adds x23, x23, x13
	umulh x13, x5, x3
	adcs x24, x24, x13
	umulh x13, x5, x4
	adcs x25, x25, x13
	str x22, [x16, #24]
	mul x13, x6, x2
	adds x23, x23, x13
	mul x13, x6, x3
	adcs x24, x24, x13
	mul x13, x6, x4
	adcs x25, x25, x13
	mul x13, x6, x5
	adcs x26, x7, x13
	adc x19, x7, x7
	umulh x13, x6, x2
	adds x24, x24, x13
	umulh x13, x6, x3
	adcs x25, x25, x13
	umulh x13, x6, x4
	adcs x26, x26, x13
	umulh x13, x6, x5
	adcs x19, x19, x13
	str x23, [x16, #32]
	mul x13, x9, x2
	adds x24, x24, x13
	mul x13, x9, x3
	adcs x25, x25, x13
	mul x13, x9, x4
	adcs x26, x26, x13
	mul x13, x9, x5
	adcs x19, x19, x13
	mul x13, x9, x6
	adcs x20, x7, x13
	adc x21, x7, x7
	umulh x13, x9, x2
	adds x25, x25, x13
	umulh x13, x9, x3
	adcs x26, x26, x13
	umulh x13, x9, x4
	adcs x19, x19, x13
	umulh x13, x9, x5
	adcs x20, x20, x13
	umulh x13, x9, x6
	adcs x21, x21, x13
	str x24, [x16, #40]
	mul x13, x11, x2
	adds x25, x25, x13
	mul x13, x11, x3
	adcs x26, x26, x13
	mul x13, x11, x4
	adcs x19, x19, x13
	mul x13, x11, x5
	adcs x20, x20, x13
	mul x13, x11, x6
	adcs x21, x21, x13
	mul x13, x11, x9
	adcs x22, x7, x13
	adc x23, x7, x7
	umulh x13, x11, x2
	adds x26, x26, x13
	umulh x13, x11, x3
	adcs x19, x19, x13
	umulh x13, x11, x4
	adcs x20, x20, x13
	umulh x13, x11, x5
	adcs x21, x21, x13
	umulh x13, x11, x6
	adcs x22, x22, x13
	umulh x13, x11, x9
	adcs x23, x23, x13
	str x25, [x16, #48]
	mul x13, x27, x2
	adds x26, x26, x13
	mul x13, x27, x3
	adcs x19, x19, x13
	mul x13, x27, x4
	adcs x20, x20, x13
	mul x13, x27, x5
	adcs x21, x21, x13
	mul x13, x27, x6
	adcs x22, x22, x13
	mul x13, x27, x9
	adcs x23, x23, x13
	mul x13, x27, x11
	adcs x24, x7, x13
	adc x25, x7, x7
	umulh x13, x27, x2
	adds x19, x19, x13
	umulh x13, x27, x3
	adcs x20, x20, x13
	umulh x13, x27, x4
	adcs x21, x21, x13
	umulh x13, x27, x5
	adcs x22, x22, x13
	umulh x13, x27, x6
	adcs x23, x23, x13
	umulh x13, x27, x9
	adcs x24, x24, x13
	umulh x13, x27, x11
	adcs x25, x25, x13
	str x26, [x16, #56]
	str x19, [x16, #64]
	str x20, [x16, #72]
	str x21, [x16, #80]
	str x22, [x16, #88]
	str x23, [x16, #96]
	str x24, [x16, #104]
	str x25, [x16, #112]
	movz x10, #0, lsl #0
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	sub x15, x15, x12
	cbnz x15, 272f
	b 273f
272:
274:
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
	cbnz x15, 274b
273:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	lsl x16, x16, #1
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x13, [x16, #64]
	adds x13, x13, x10
	str x13, [x16, #64]
	ldr x13, [x16, #72]
	adcs x13, x13, x7
	str x13, [x16, #72]
	ldr x13, [x16, #80]
	adcs x13, x13, x7
	str x13, [x16, #80]
	ldr x13, [x16, #88]
	adcs x13, x13, x7
	str x13, [x16, #88]
	ldr x13, [x16, #96]
	adcs x13, x13, x7
	str x13, [x16, #96]
	ldr x13, [x16, #104]
	adcs x13, x13, x7
	str x13, [x16, #104]
	ldr x13, [x16, #112]
	adcs x13, x13, x7
	str x13, [x16, #112]
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 271b
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x9, [x0, #112]
	ldr x12, [x0, #48]
	add x16, x8, #0
	add x11, x9, #0
	lsr x14, x12, #2
	adds x5, x7, x7
275:
	ldr x1, [x11, #0]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #0]
	str x6, [x16, #8]
	ldr x1, [x11, #8]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #16]
	ldr x4, [x16, #24]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #16]
	str x6, [x16, #24]
	ldr x1, [x11, #16]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #32]
	ldr x4, [x16, #40]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #32]
	str x6, [x16, #40]
	ldr x1, [x11, #24]
	mul x2, x1, x1
	umulh x1, x1, x1
	ldr x3, [x16, #48]
	ldr x4, [x16, #56]
	extr x6, x4, x3, #63
	extr x3, x3, x5, #63
	add x5, x4, #0
	adcs x3, x3, x2
	adcs x6, x6, x1
	str x3, [x16, #48]
	str x6, [x16, #56]
	add x16, x16, #64
	add x11, x11, #32
	sub x14, x14, #1
	cbnz x14, 275b
	lsr x5, x5, #63
	adc x5, x5, x7
	str x5, [x16, #0]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
276:
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
277:
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
	cbnz x15, 277b
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
	cbnz x12, 276b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	lsl x14, x12, #3
	add x14, x8, x14
	ldr x15, [x14, #0]
	sub x15, x7, x15
	lsr x14, x12, #2
	subs x3, x7, x7
278:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x5, #0]
	ldr x3, [x16, #8]
	ldr x4, [x17, #8]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x5, #8]
	ldr x3, [x16, #16]
	ldr x4, [x17, #16]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x5, #16]
	ldr x3, [x16, #24]
	ldr x4, [x17, #24]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x5, #24]
	add x16, x16, #32
	add x17, x17, #32
	add x5, x5, #32
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 270b
	ldr x12, [x0, #48]
	add x6, x12, #2
	lsl x6, x6, #3
	lsr x13, x12, #3
	ldr x5, [x0, #216]
	dup v22.2d, x5
	movz x2, #1, lsl #0
	dup v24.2d, x2
	ldr x17, [x0, #104]
279:
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
280:
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
	cbnz x14, 280b
	str q16, [x17, #0]
	str q17, [x17, #16]
	str q18, [x17, #32]
	str q19, [x17, #48]
	add x17, x17, #64
	sub x13, x13, #1
	cbnz x13, 279b
	ldr x3, [x0, #200]
	lsl x4, x6, #5
	add x3, x3, x4
	str x3, [x0, #208]
	movz x3, #32, lsl #0
	str x3, [x0, #224]
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, x12
	lsr x14, x14, #3
281:
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
	cbnz x14, 281b
	str x7, [x16, #0]
	str x7, [x16, #8]
	ldr x8, [x0, #112]
	lsr x12, x12, #3
282:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
283:
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
	cbnz x15, 283b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 282b
	ldr x8, [x0, #80]
	add x8, x8, #16
	ldr x12, [x0, #48]
	lsr x12, x12, #3
	movz x10, #0, lsl #0
284:
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
285:
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
	cbnz x15, 285b
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
	cbnz x12, 284b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x5, [x0, #112]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
286:
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
	cbnz x14, 286b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
287:
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
	cbnz x14, 287b
	umov x19, v0.d[0]
	umov x20, v1.d[0]
	umov x21, v2.d[0]
	umov x22, v3.d[0]
	umov x23, v4.d[0]
	umov x24, v5.d[0]
	umov x25, v6.d[0]
	umov x26, v27.d[0]
	umov x27, v28.d[0]
	umov x28, v29.d[0]
	umov x30, v30.d[0]
	movz x3, #0, lsl #0
	str x3, [x0, #216]
	str x3, [x0, #160]
236:
21:
	ret
	.p2align 6

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
	lsr x3, x12, #21
	cbz x3, 235f
	lsl x6, x12, #7
237:
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
238:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
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
239:
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
	cbnz x14, 239b
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
240:
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
	cbnz x14, 240b
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
241:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 241b
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
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
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
245:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 245b
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
246:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 246b
	sub x6, x6, #1
	cbnz x6, 237b
	b 236f
235:
	mov v19.d[0], x1
	mov v19.d[1], x2
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
247:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 247b
	adc x3, x7, x7
	str x3, [x5, #0]
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
248:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 248b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x11, #0
	add x3, x3, x0
	add x3, x3, #256
	ldr x3, [x3, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
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
	mov v18.d[1], x15
	movz x3, #1, lsl #0
	mov v18.d[0], x3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x4, [x16, #0]
	orr x4, x4, x3
	str x4, [x16, #0]
	add x15, x12, x12
	add x15, x15, x12
	add x15, x15, #2
250:
	add x2, x11, #0
	add x2, x2, x2
	add x2, x2, x11
	add x2, x2, x0
	add x2, x2, #256
	ldr x2, [x2, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x0
	add x3, x3, #256
	ldr x3, [x3, #0]
	umov x1, v18.d[0]
	lsl x14, x11, #32
	add x14, x14, x12
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	mov v18.d[0], x1
	mov v16.d[0], x4
	mov v16.d[1], x5
	mov v17.d[0], x6
	mov v17.d[1], x7
	lsr x11, x14, #32
	lsl x13, x11, #32
	sub x12, x14, x13
	sub x15, x15, #1
	umov x4, v16.d[0]
	umov x5, v16.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
251:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 251b
	umov x4, v17.d[0]
	umov x5, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
252:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 252b
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
	add x14, x12, #0
253:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 253b
	ldr x3, [x16, #0]
	lsr x4, x3, #63
	movz x13, #0, lsl #0
	sub x4, x13, x4
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
254:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x3, [x16, #0]
	lsr x4, x3, #63
	movz x13, #0, lsl #0
	sub x4, x13, x4
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	umov x4, v16.d[0]
	umov x5, v16.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
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
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
255:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 255b
	umov x4, v17.d[0]
	umov x5, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
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
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
256:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 256b
	umov x5, v18.d[1]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	mul x1, x3, x5
	lsl x6, x12, #3
	add x6, x8, x6
	ldr x3, [x6, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x3, x7, x3
	str x3, [x6, #8]
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x16, x16, #8
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
258:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 258b
	umov x5, v18.d[1]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	mul x1, x3, x5
	lsl x6, x12, #3
	add x6, x8, x6
	ldr x3, [x6, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x3, x7, x3
	str x3, [x6, #8]
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
259:
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
	cbnz x14, 259b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x16, x16, #8
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
	cbnz x15, 250b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
	movz x7, #0, lsl #0
	adds x3, x15, x15
261:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
	movz x7, #0, lsl #0
	adds x3, x15, x15
262:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 262b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x8, x11, #0
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
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
263:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 263b
	ldr x3, [x5, #0]
	adc x3, x3, x7
	str x3, [x5, #0]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x8, x11, #0
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
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
264:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x3, [x5, #0]
	adc x3, x3, x7
	str x3, [x5, #0]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x6, x11, #0
	add x6, x6, x6
	add x6, x6, x6
	add x6, x6, x6
	add x6, x6, x0
	add x6, x6, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	movz x7, #0, lsl #0
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	lsl x15, x12, #4
	sub x15, x15, x12
	add x15, x15, #10
267:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	add x10, x11, #0
	add x10, x10, x0
	add x10, x10, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x6, x11, #0
	add x6, x6, x6
	add x6, x6, x0
	add x6, x6, #256
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
268:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	sub x15, x15, #1
	cbnz x15, 267b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
236:
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 272b
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
273:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
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
274:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 274b
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
275:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 275b
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
276:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
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
277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 277b
	lsl x6, x12, #6
278:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
279:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 279b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
280:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 280b
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
282:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 282b
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
	cbnz x6, 278b
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
283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 283b
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
284:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
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
286:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 286b
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
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
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
288:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 288b
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
289:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 289b
	lsl x6, x12, #6
290:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
291:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 291b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
292:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 292b
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
293:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 293b
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
294:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 294b
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
	cbnz x6, 290b
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
295:
	and x5, x2, x6
	cbz x5, 296f
	b 297f
296:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
297:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 295b
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
298:
	and x5, x2, x6
	cbz x5, 299f
	b 2100f
299:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2100:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 298b
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
2101:
	and x5, x2, x6
	cbz x5, 2102f
	b 2103f
2102:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2103:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2101b
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
2104:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2104b
	ldr x1, [x0, #152]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2105:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2105b
	ldr x1, [x0, #160]
	ldr x2, [x0, #168]
	movz x3, #0, lsl #0
2106:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2106b
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
	lsr x3, x12, #21
	cbz x3, 289f
	lsl x6, x12, #7
291:
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
292:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
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
293:
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
	cbnz x14, 293b
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
294:
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
	cbnz x14, 294b
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
295:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 295b
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
296:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 296b
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
298:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
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
299:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 299b
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
2100:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	sub x6, x6, #1
	cbnz x6, 291b
	b 290f
289:
	mov v19.d[0], x1
	mov v19.d[1], x2
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x0, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2101:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	adc x3, x7, x7
	str x3, [x5, #0]
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
2102:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
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
2103:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x0, #256
	ldr x3, [x3, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
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
	mov v18.d[1], x15
	movz x3, #1, lsl #0
	mov v18.d[0], x3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x4, [x16, #0]
	orr x4, x4, x3
	str x4, [x16, #0]
	add x15, x12, x12
	add x15, x15, x12
	add x15, x15, #2
2104:
	add x2, x11, #0
	add x2, x2, x2
	add x2, x2, x2
	add x2, x2, x2
	add x2, x2, x11
	add x2, x2, x0
	add x2, x2, #256
	ldr x2, [x2, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x0
	add x3, x3, #256
	ldr x3, [x3, #0]
	umov x1, v18.d[0]
	lsl x14, x11, #32
	add x14, x14, x12
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	mov v18.d[0], x1
	mov v16.d[0], x4
	mov v16.d[1], x5
	mov v17.d[0], x6
	mov v17.d[1], x7
	lsr x11, x14, #32
	lsl x13, x11, #32
	sub x12, x14, x13
	sub x15, x15, #1
	umov x4, v16.d[0]
	umov x5, v16.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
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
	add x14, x12, #1
	movz x13, #0, lsl #0
2105:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	umov x4, v17.d[0]
	umov x5, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
2106:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2106b
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
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2107:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x3, [x16, #0]
	lsr x4, x3, #63
	movz x13, #0, lsl #0
	sub x4, x13, x4
	extr x3, x4, x3, #59
	str x3, [x17, #0]
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
	add x14, x12, #0
2108:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x3, [x16, #0]
	lsr x4, x3, #63
	movz x13, #0, lsl #0
	sub x4, x13, x4
	extr x3, x4, x3, #59
	str x3, [x17, #0]
	umov x4, v16.d[0]
	umov x5, v16.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
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
	add x17, x17, x17
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
	add x14, x12, #1
	movz x13, #0, lsl #0
2109:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	umov x4, v17.d[0]
	umov x5, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
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
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	add x14, x12, #1
	movz x13, #0, lsl #0
2110:
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x6, x4, x2
	umulh x7, x4, x2
	and x2, x2, x9
	sub x7, x7, x2
	mul x2, x5, x3
	umulh x1, x5, x3
	and x3, x3, x10
	sub x1, x1, x3
	lsr x3, x13, #63
	sub x3, x3, #1
	adds x6, x6, x2
	adc x7, x7, x1
	adds x6, x6, x13
	sbc x13, x7, x3
	str x6, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	umov x5, v18.d[1]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	mul x1, x3, x5
	lsl x6, x12, #3
	add x6, x8, x6
	ldr x3, [x6, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x3, x7, x3
	str x3, [x6, #8]
	add x9, x0, #256
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x16, x16, #8
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
2112:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	umov x5, v18.d[1]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x3, [x8, #0]
	mul x1, x3, x5
	lsl x6, x12, #3
	add x6, x8, x6
	ldr x3, [x6, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x3, x7, x3
	str x3, [x6, #8]
	add x9, x0, #256
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x16, x16, #8
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
2114:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	cbnz x15, 2104b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
	movz x7, #0, lsl #0
	adds x3, x15, x15
2115:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
	movz x7, #0, lsl #0
	adds x3, x15, x15
2116:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x0, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
2117:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x3, [x5, #0]
	adc x3, x3, x7
	str x3, [x5, #0]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x15, x7, x3
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x0, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
2118:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	ldr x3, [x5, #0]
	adc x3, x3, x7
	str x3, [x5, #0]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x10, x0, #256
	add x6, x11, #0
	add x6, x6, x6
	add x6, x6, x11
	add x6, x6, x6
	add x6, x6, x11
	add x6, x6, x6
	add x6, x6, x11
	add x6, x6, x0
	add x6, x6, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2119:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2120:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	lsl x15, x12, #4
	sub x15, x15, x12
	add x15, x15, #10
2121:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
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
	add x6, x11, #0
	add x6, x6, x6
	add x6, x6, x6
	add x6, x6, x6
	add x6, x6, x0
	add x6, x6, #256
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2122:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	sub x15, x15, #1
	cbnz x15, 2121b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
290:
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
2125:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2125b
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
2126:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2126b
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
2127:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	lsl x6, x12, #6
2128:
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
2129:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2130:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2130b
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
2131:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2131b
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
2132:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2132b
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
	cbnz x6, 2128b
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
2133:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2133b
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
2134:
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
	cbnz x14, 2134b
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
2135:
	and x5, x2, x6
	cbz x5, 2136f
	b 2137f
2136:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2137:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2135b
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
2138:
	and x5, x2, x6
	cbz x5, 2139f
	b 2140f
2139:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2140:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2138b
	ldr x3, [x0, #176]
	movz x4, #1, lsl #0
	and x0, x3, x4
220:
	b 21f
20:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2141:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2141b
	ldr x1, [x0, #168]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2142:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2142b
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

vg_rsa_mul_5_1_4:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #96]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_5_6:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #104]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #104]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #112]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_4_7:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #96]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_5_5_4:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #104]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #96]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_6_5:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #104]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_6_7:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #112]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_1_1_4:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #72]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #72]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #96]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
	ldr x16, [x0, #72]
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #72]
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
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_5_1:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #104]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #72]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_5_1_7:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_1_1_6:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #72]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #72]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #72]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #112]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
	ldr x16, [x0, #72]
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #72]
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
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_4_4_7:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
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
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
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
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #96]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #120]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
	ldr x16, [x0, #96]
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
	ldr x12, [x0, #48]
	lsl x16, x12, #3
	add x16, x8, x16
	str x10, [x16, #0]
	str x7, [x16, #8]
	ldr x10, [x0, #64]
	ldr x16, [x0, #96]
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
	ldr x5, [x0, #96]
	ldr x6, [x0, #80]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	lsr x14, x12, #2
	subs x3, x7, x7
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
	ret
	.p2align 6

vg_rsa_mul_6_4_6:
	ldr x12, [x0, #48]
	lsr x3, x12, #4
	movz x4, #7, lsl #0
	and x4, x12, x4
	cbnz x3, 20f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
22:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 22b
	add x13, x12, #0
23:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
24:
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
	cbnz x14, 24b
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
25:
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
	cbnz x14, 25b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 23b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
26:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 26b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
27:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 27b
	b 21f
20:
	cbz x4, 28f
	ldr x8, [x0, #80]
	ldr x9, [x0, #112]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 210b
	add x13, x12, #0
211:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
212:
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
	cbnz x14, 212b
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
213:
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
	cbnz x14, 213b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 211b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
215:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 215b
	b 29f
28:
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
216:
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
	cbnz x14, 216b
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
217:
	ldr x17, [x0, #96]
	sub x16, x8, x17
	ldr x13, [x0, #80]
	add x13, x13, #16
	add x16, x16, x13
	ldr x17, [x0, #112]
	ldr x15, [x0, #48]
	lsr x15, x15, #3
	movz x10, #0, lsl #0
218:
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
	cbnz x15, 218b
	add x8, x8, #64
	sub x12, x12, #1
	cbnz x12, 217b
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
219:
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
220:
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
	cbnz x15, 220b
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
	cbnz x12, 219b
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
221:
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
	cbnz x14, 221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	lsr x14, x12, #2
222:
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
	cbnz x14, 222b
29:
21:
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
