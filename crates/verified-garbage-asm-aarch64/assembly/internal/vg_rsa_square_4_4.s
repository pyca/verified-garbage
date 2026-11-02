// The functions of `src/internal/vg_rsa_square_4_4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
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
