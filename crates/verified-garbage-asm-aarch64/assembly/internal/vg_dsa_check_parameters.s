// The functions of `src/internal/vg_dsa_check_parameters.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_check_parameters:
	add x11, x4, #0
	movz x12, #0, lsl #0
	str x12, [x11, #296]
	str x12, [x11, #320]
	str x12, [x11, #304]
	str x12, [x11, #312]
	str x12, [x11, #344]
	str x0, [x11, #256]
	str x2, [x11, #328]
	str x3, [x11, #336]
	ldr x3, [x11, #256]
	ldr x12, [x11, #328]
	add x3, x3, x12
	str x3, [x11, #264]
	ldr x13, [x11, #336]
	add x3, x3, x13
	str x3, [x11, #272]
	add x3, x3, x12
	str x3, [x11, #280]
	add x3, x3, x12
	str x3, [x11, #288]
	add x0, x11, #0
	ldr x3, [x11, #272]
	str x3, [x11, #280]
	ldr x1, [x0, #256]
	ldr x9, [x0, #328]
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
20:
	ldrb w3, [x1, #0]
	cbz x8, 21f
	b 22f
21:
	cbnz x3, 23f
	b 24f
23:
	add x8, x9, #0
	add x10, x3, #0
24:
22:
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 20b
	str x8, [x0, #176]
	lsr x3, x10, #7
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #360]
	ldr x1, [x0, #264]
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
25:
	ldrb w3, [x1, #0]
	cbz x8, 26f
	b 27f
26:
	cbnz x3, 28f
	b 29f
28:
	add x8, x9, #0
	add x10, x3, #0
29:
27:
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 25b
	str x8, [x0, #352]
	lsr x3, x10, #7
	movz x4, #0, lsl #0
	sub x3, x4, x3
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x2, [x0, #176]
	sub x6, x2, #128
	cbz x6, 210f
	sub x6, x2, #256
	cbz x6, 212f
	sub x6, x2, #384
	cbz x6, 214f
	movz x3, #0, lsl #0
	b 215f
214:
	movz x3, #32, lsl #0
	eor x3, x8, x3
	tst x3, x3
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
215:
	b 213f
212:
	movz x3, #28, lsl #0
	eor x3, x8, x3
	tst x3, x3
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	add x11, x3, #0
	movz x3, #32, lsl #0
	eor x3, x8, x3
	tst x3, x3
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	orr x3, x3, x11
	add x11, x3, #0
	movz x3, #20, lsl #0
	eor x3, x8, x3
	tst x3, x3
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	orr x3, x3, x11
213:
	b 211f
210:
	movz x3, #20, lsl #0
	eor x3, x8, x3
	tst x3, x3
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
211:
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x1, [x0, #256]
	ldr x9, [x0, #328]
	sub x9, x9, #1
	add x1, x1, x9
	ldrb w3, [x1, #0]
	ldr x1, [x0, #264]
	ldr x9, [x0, #336]
	sub x9, x9, #1
	add x1, x1, x9
	ldrb w2, [x1, #0]
	and x3, x3, x2
	movz x2, #1, lsl #0
	and x3, x3, x2
	movz x2, #0, lsl #0
	sub x3, x2, x3
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #344]
	ldr x2, [x0, #352]
	subs x4, x2, x3
	csel x3, x3, x2, hs
	str x3, [x0, #352]
	ldr x3, [x0, #360]
	cbz x3, 216f
	movz x12, #48, lsl #0
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
	ldr x3, [x0, #256]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	add x1, x0, #0
	ldr x12, [x0, #136]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x4, #3456, lsl #0
	add x0, x0, x4
	str x12, [x0, #48]
	str x1, [x0, #128]
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
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 218b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #64]
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
	ldr x3, [x0, #64]
	ldr x3, [x3, #0]
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
	ldr x0, [x0, #128]
	ldr x3, [x0, #264]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	add x1, x0, #0
	ldr x12, [x0, #136]
	add x12, x12, #7
	lsr x12, x12, #3
	movz x4, #13312, lsl #0
	add x0, x0, x4
	str x12, [x0, #48]
	str x1, [x0, #128]
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
	ldr x8, [x0, #64]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
222:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #64]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
223:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 224f
	b 225f
224:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
225:
	cbnz x2, 223b
	ldr x3, [x0, #64]
	ldr x3, [x3, #0]
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
	ldr x0, [x0, #128]
	ldr x3, [x0, #272]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	movz x4, #3456, lsl #0
	add x0, x0, x4
	ldr x8, [x0, #72]
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
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
230:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
231:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 231b
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x5, x3, x4, hs
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, ne
	and x3, x3, x5
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #280]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	movz x4, #3456, lsl #0
	add x0, x0, x4
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
232:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 232b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
233:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 234f
	b 235f
234:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
235:
	cbnz x2, 233b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
236:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 236b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
237:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x5, x3, x4, hs
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, ne
	and x3, x3, x5
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	str x3, [x0, #160]
	ldr x3, [x0, #328]
	str x3, [x0, #168]
	movz x4, #3456, lsl #0
	add x0, x0, x4
	ldr x14, [x0, #48]
	ldr x16, [x0, #64]
	ldr x17, [x0, #112]
	movz x4, #1, lsl #0
	movz x7, #0, lsl #0
	ldr x3, [x16, #0]
	subs x3, x3, x4
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
238:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
239:
	and x5, x2, x6
	cbz x5, 240f
	b 241f
240:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
241:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 239b
	ldr x0, [x0, #128]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	str x3, [x0, #160]
	ldr x3, [x0, #336]
	str x3, [x0, #168]
	movz x4, #13312, lsl #0
	add x0, x0, x4
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
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
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 243f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 245f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
247:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 247b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
248:
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
	cbnz x13, 248b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
249:
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
250:
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
	cbnz x14, 250b
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
251:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 251b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 249b
	b 246f
245:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 252f
254:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 254b
	b 253f
252:
253:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
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
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
256:
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
257:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
258:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
259:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 256b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
260:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 260b
246:
	b 244f
243:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
261:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
262:
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
263:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 262b
244:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_4}
	umov x30, v31.d[0]
	ldr x8, [x0, #112]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
267:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
268:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 269f
271:
	ldr x1, [x0, #184]
	ldrb w3, [x1, #0]
	ldr x8, [x0, #72]
	str x3, [x8, #0]
	add x1, x1, #1
	str x1, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_6}
	umov x30, v31.d[0]
	ldr x9, [x0, #112]
	ldr x17, [x0, #72]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x5, [x0, #112]
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
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 271b
	b 270f
269:
270:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
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
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
278:
	ldrb w3, [x1, #0]
	orr x8, x8, x3
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 278b
	tst x8, x8
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	movz x3, #14912, lsl #0
	add x3, x0, x3
	str x3, [x0, #160]
	ldr x3, [x0, #336]
	str x3, [x0, #168]
	movz x4, #13312, lsl #0
	add x0, x0, x4
	ldr x14, [x0, #48]
	ldr x16, [x0, #64]
	ldr x17, [x0, #112]
	movz x4, #2, lsl #0
	movz x7, #0, lsl #0
	ldr x3, [x16, #0]
	subs x3, x3, x4
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
279:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
280:
	and x5, x2, x6
	cbz x5, 281f
	b 282f
281:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
282:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 280b
	ldr x0, [x0, #128]
	ldr x3, [x0, #272]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	ldr x3, [x0, #264]
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	str x3, [x0, #160]
	ldr x3, [x0, #328]
	str x3, [x0, #168]
	movz x4, #3456, lsl #0
	add x0, x0, x4
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
283:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 283b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 284f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 286f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
288:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 288b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
289:
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
	cbnz x13, 289b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
290:
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
291:
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
	cbnz x14, 291b
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
292:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 290b
	b 287f
286:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 293f
295:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 295b
	b 294f
293:
294:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
296:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 296b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
297:
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
298:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 298b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 297b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2101:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2101b
287:
	b 285f
284:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2102:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2103:
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
2104:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x16, x8, #0
	add x14, x12, #0
2106:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2103b
285:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2107:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2108:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2109f
	b 2110f
2109:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2110:
	cbnz x2, 2108b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #104]
	ldr x17, [x0, #96]
	add x14, x12, #0
2111:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	ldr x5, [x0, #128]
	ldr x3, [x5, #144]
	str x3, [x0, #136]
	ldr x3, [x5, #152]
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
2112:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
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
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #208]
	add x14, x12, #0
2113:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2114:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2115:
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
2116:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2115b
2117:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2118:
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
	ldr x3, [x0, #216]
	cbz x3, 2119f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2121:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2120f
2119:
2120:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2118b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2117b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_7}
	umov x30, v31.d[0]
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
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
	ldr x0, [x0, #128]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	movz x4, #3456, lsl #0
	add x0, x0, x4
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2125:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2125b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2126:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2127f
	b 2128f
2127:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2128:
	cbnz x2, 2126b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2129:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #360]
	movz x0, #1, lsl #0
	and x0, x3, x0
	b 217f
216:
	movz x0, #0, lsl #0
217:
	ret
	.p2align 6
