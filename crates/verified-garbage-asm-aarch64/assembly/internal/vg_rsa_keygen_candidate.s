// The functions of `src/internal/vg_rsa_keygen_candidate.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_candidate:
	ldr x8, [sp, #8]
	str x0, [x8, #128]
	str x1, [x8, #144]
	str x2, [x8, #136]
	str x3, [x8, #152]
	str x4, [x8, #160]
	str x5, [x8, #168]
	str x6, [x8, #184]
	str x7, [x8, #192]
	ldr x9, [sp, #0]
	str x9, [x8, #200]
	add x0, x8, #0
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
20:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 20b
	ldr x3, [x0, #200]
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 21f
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
23:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 23b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	orr x3, x3, x4
	str x3, [x16, #0]
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x3, [x5, #0]
	movz x4, #49152, lsl #48
	orr x3, x3, x4
	str x3, [x5, #0]
	ldr x3, [x0, #144]
	str x3, [x0, #216]
	ldr x3, [x0, #184]
	movz x15, #0, lsl #0
	cbz x3, 27f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #168]
	ldr x2, [x0, #184]
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
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
213:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 213b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #208]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	ldr x15, [x0, #208]
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
215:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 215b
	ldr x12, [x0, #48]
	movz x9, #4096, lsl #16
	sub x13, x12, #2
	ldr x8, [x0, #112]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
216:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 216b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
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
	add x17, x17, x0
	add x17, x17, #256
217:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 217b
	sub x4, x7, #1
	csel x15, x4, x7, hs
	b 28f
27:
28:
	cbnz x15, 218f
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
220:
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
221:
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
	cbnz x14, 221b
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
222:
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
	cbnz x14, 222b
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
223:
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
	cbnz x14, 223b
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
224:
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
	cbnz x14, 224b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	cbnz x10, 220b
	cbnz x1, 225f
	ldr x1, [x0, #152]
	ldr x2, [x0, #160]
	movz x3, #0, lsl #0
227:
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 227b
	str x3, [x0, #8]
	movz x4, #1, lsl #0
	and x5, x3, x4
	cbz x5, 228f
	sub x5, x3, #1
	cbz x5, 230f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
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
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	eor x3, x3, x4
	str x3, [x16, #0]
	lsl x5, x12, #3
	add x10, x16, x5
	add x14, x12, #0
	ldr x13, [x0, #8]
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
233:
	sub x10, x10, #8
	ldr x2, [x10, #0]
	movz x9, #64, lsl #0
234:
	adds x2, x2, x2
	adcs x3, x3, x3
	adc x4, x7, x7
	subs x5, x3, x13
	csel x6, x8, x7, hs
	sub x4, x7, x4
	orr x6, x6, x4
	eor x5, x5, x3
	and x5, x5, x6
	eor x3, x3, x5
	sub x9, x9, #1
	cbnz x9, 234b
	sub x14, x14, #1
	cbnz x14, 233b
	movz x9, #128, lsl #0
235:
	movz x4, #1, lsl #0
	and x4, x3, x4
	sub x4, x7, x4
	subs x5, x3, x13
	csel x6, x7, x8, hs
	eor x5, x5, x6
	sub x5, x5, x6
	eor x10, x3, x13
	and x10, x10, x6
	eor x10, x10, x13
	eor x5, x5, x3
	and x5, x5, x4
	eor x3, x3, x5
	eor x10, x10, x13
	and x10, x10, x4
	eor x13, x13, x10
	lsr x3, x3, #1
	sub x9, x9, #1
	cbnz x9, 235b
	str x13, [x0, #8]
	b 231f
230:
231:
	b 229f
228:
229:
	ldr x3, [x0, #8]
	sub x3, x3, #1
	cbnz x3, 236f
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
238:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 238b
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
	cbz x3, 239f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
241:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 241b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
242:
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
	cbnz x13, 242b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
243:
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
244:
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
	cbnz x14, 244b
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
245:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 243b
	b 240f
239:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 246f
248:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 248b
	b 247f
246:
247:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
250:
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
251:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 251b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
252:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 252b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
253:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 253b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 250b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
254:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 254b
240:
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
261:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 261b
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
262:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 262b
	ldr x12, [x0, #48]
	movz x5, #27, lsl #0
	movz x4, #5, lsl #0
	subs x3, x12, x4
	movz x6, #8, lsl #0
	csel x5, x6, x5, hs
	movz x4, #6, lsl #0
	subs x3, x12, x4
	movz x6, #7, lsl #0
	csel x5, x6, x5, hs
	movz x4, #7, lsl #0
	subs x3, x12, x4
	movz x6, #6, lsl #0
	csel x5, x6, x5, hs
	movz x4, #8, lsl #0
	subs x3, x12, x4
	movz x6, #5, lsl #0
	csel x5, x6, x5, hs
	movz x4, #22, lsl #0
	subs x3, x12, x4
	movz x6, #4, lsl #0
	csel x5, x6, x5, hs
	movz x4, #59, lsl #0
	subs x3, x12, x4
	movz x6, #3, lsl #0
	csel x5, x6, x5, hs
	str x5, [x0, #152]
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
263:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 263b
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
264:
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
	cbnz x14, 264b
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
265:
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
	cbnz x14, 265b
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
266:
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
	cbnz x14, 266b
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
267:
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
	cbnz x14, 267b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #160]
	movz x3, #0, lsl #0
	str x3, [x0, #168]
268:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 269f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
272:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 273f
	b 274f
273:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
274:
	cbnz x2, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
275:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 275b
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
276:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
	csel x15, x7, x8, hs
	and x9, x9, x15
	str x9, [x0, #0]
	eor x9, x9, x8
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	movz x4, #2, lsl #0
	and x4, x4, x9
	ldr x3, [x16, #0]
	orr x3, x3, x4
	str x3, [x16, #0]
	lsl x5, x12, #3
	add x16, x16, x5
	sub x16, x16, #8
	movz x4, #32768, lsl #48
	and x4, x4, x9
	eor x4, x4, x8
	ldr x3, [x16, #0]
	and x3, x3, x4
	str x3, [x16, #0]
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
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
283:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
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
	bl {vg_miller_rabin_round}
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
	cbz x3, 284f
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
	b 285f
284:
	movz x3, #3, lsl #0
	str x3, [x0, #248]
285:
	b 270f
269:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
270:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 268b
	ldr x3, [x0, #248]
	cbz x3, 286f
	sub x3, x3, #1
	cbz x3, 288f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #3, lsl #0
	b 289f
288:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
290:
	and x5, x2, x6
	cbz x5, 291f
	b 292f
291:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
292:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 290b
	movz x0, #1, lsl #0
289:
	b 287f
286:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
287:
	b 237f
236:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #3, lsl #0
237:
	b 226f
225:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #3, lsl #0
226:
	b 219f
218:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
219:
	b 22f
21:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6
