// The functions of `src/internal/vg_rsa_keygen_key.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
	ldr x8, [sp, #64]
	str x0, [x8, #128]
	str x1, [x8, #144]
	str x2, [x8, #136]
	str x4, [x8, #168]
	str x5, [x8, #184]
	str x6, [x8, #192]
	ldr x9, [sp, #0]
	str x9, [x8, #200]
	ldr x9, [sp, #16]
	str x9, [x8, #208]
	ldr x9, [sp, #32]
	str x9, [x8, #216]
	ldr x9, [sp, #48]
	str x9, [x8, #152]
	ldr x9, [sp, #56]
	str x9, [x8, #160]
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
20:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 20b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x2, [x0, #184]
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
24:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 24b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
25:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 26f
	b 27f
26:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
27:
	cbnz x2, 25b
	ldr x1, [x0, #152]
	ldr x2, [x0, #160]
	movz x3, #0, lsl #0
28:
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 28b
	str x3, [x0, #240]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
29:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 29b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
210:
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
	cbnz x14, 210b
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
211:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 211b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
212:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 212b
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
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 214b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
215:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
216:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 216b
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
217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 217b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
218:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
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
219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 219b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
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
220:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 220b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x4, x7, hs
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
221:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
222:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 222b
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
223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x11, x16, #0
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
224:
	ldr x1, [x11, #0]
	add x11, x11, #8
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
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
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
227:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 227b
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
228:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 228b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
229:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsl x6, x12, #6
230:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	ldr x4, [x17, #0]
	orr x3, x3, x4
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
231:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
232:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 232b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x0
	add x17, x17, #256
233:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 233b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x0
	add x17, x17, #256
234:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
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
	add x17, x17, x0
	add x17, x17, #256
235:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 235b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
236:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 236b
	sub x6, x6, #1
	cbnz x6, 230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
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
238:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #2, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
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
	str x15, [x0, #248]
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
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #3, lsl #0
	str x3, [x16, #0]
	ldr x15, [x0, #248]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
241:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 241b
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
242:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 242b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x14, x12, #0
243:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 243b
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
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
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
245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsr x3, x12, #21
	cbz x3, 246f
	lsl x6, x12, #7
248:
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
249:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 249b
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
250:
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
	cbnz x14, 250b
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
251:
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
	cbnz x14, 251b
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
252:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 252b
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
253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 253b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
254:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 254b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
255:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
256:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 256b
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
257:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 257b
	sub x6, x6, #1
	cbnz x6, 248b
	b 247f
246:
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
258:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 258b
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
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
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
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x11
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
261:
	mov v20.d[0], x19
	mov v20.d[1], x20
	mov v21.d[0], x21
	mov v21.d[1], x22
	mov v22.d[0], x23
	mov v22.d[1], x24
	mov v23.d[0], x25
	mov v23.d[1], x26
	mov v24.d[0], x27
	mov v24.d[1], x28
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
	umov x6, v17.d[0]
	umov x7, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	lsr x19, x6, #63
	sub x19, x13, x19
	lsr x20, x7, #63
	sub x20, x13, x20
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x26, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x26, x26, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x26, x26, x13
	sbc x13, x21, x22
	mul x27, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x27, x27, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x27, x27, x25
	sbc x25, x21, x22
	add x14, x12, #0
262:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x1, x1, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	mul x24, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x24, x24, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	extr x22, x1, x26, #59
	str x22, [x16, #0]
	add x26, x1, #0
	extr x22, x24, x27, #59
	str x22, [x17, #0]
	add x27, x24, #0
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 262b
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	extr x22, x13, x26, #59
	str x22, [x16, #0]
	extr x22, x25, x27, #59
	str x22, [x17, #0]
	umov x28, v18.d[1]
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
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	sub x14, x12, #1
	mov v25.d[0], x30
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x22, x4, x2
	madd x22, x5, x3, x22
	mul x26, x22, x28
	mul x22, x6, x2
	madd x22, x7, x3, x22
	mul x27, x22, x28
	movz x28, #0, lsl #0
	movz x23, #0, lsl #0
	movz x30, #0, lsl #0
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	cbz x14, 263f
265:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	str x1, [x16, #0]
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 265b
	b 264f
263:
264:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	adds x1, x1, x23
	adc x13, x13, x28
	str x1, [x16, #0]
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	adds x24, x24, x30
	adc x25, x25, x28
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	str x13, [x16, #0]
	str x25, [x17, #0]
	umov x30, v25.d[0]
	umov x19, v20.d[0]
	umov x20, v20.d[1]
	umov x21, v21.d[0]
	umov x22, v21.d[1]
	umov x23, v22.d[0]
	umov x24, v22.d[1]
	umov x25, v23.d[0]
	umov x26, v23.d[1]
	umov x27, v24.d[0]
	umov x28, v24.d[1]
	cbnz x15, 261b
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
266:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
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
267:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
268:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 268b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
269:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 269b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
272:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
273:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
274:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 274b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
275:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 275b
	sub x15, x15, #1
	cbnz x15, 272b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
247:
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
276:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 276b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x15, [x0, #248]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
277:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 277b
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
278:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 278b
	lsl x6, x12, #6
279:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
280:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 280b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
281:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 281b
	movz x7, #0, lsl #0
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
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x0
	add x13, x13, #256
282:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 282b
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
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
283:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
	add x16, x11, #0
	add x16, x16, x16
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
	cbnz x6, 279b
	ldr x3, [x0, #240]
	cbz x3, 284f
	sub x3, x3, #1
	cbz x3, 286f
	ldr x3, [x0, #240]
	movz x4, #1, lsl #0
	and x3, x3, x4
	cbnz x3, 288f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
290:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #240]
	str x3, [x16, #0]
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
291:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 291b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x14, x12, #0
292:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
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
293:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 293b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
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
294:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 294b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
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
	movz x4, #1, lsl #0
	and x4, x15, x4
	orr x3, x3, x4
	str x3, [x16, #0]
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
295:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 295b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
296:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 296b
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
297:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 297b
	lsl x6, x12, #6
298:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
299:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 299b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2100:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	movz x7, #0, lsl #0
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
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2102:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
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
	cbnz x6, 298b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2104:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2104b
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
2105:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #3, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2106:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x10, x15, #0
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
	and x3, x3, x4
	sub x15, x3, #1
	orr x15, x15, x10
	add x10, x15, #0
	movz x7, #0, lsl #0
	sub x4, x7, #1
	eor x15, x15, x4
	str x15, [x0, #248]
	add x15, x10, #0
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
2107:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x14, x12, #0
2108:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
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
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
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
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2111:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2111b
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
2112:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2112b
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
2113:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsr x3, x12, #21
	cbz x3, 2114f
	lsl x6, x12, #7
2116:
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
2117:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2117b
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
2118:
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
	cbnz x14, 2118b
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
2119:
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
	cbnz x14, 2119b
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
2120:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2120b
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
2121:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2122:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2123:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2123b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2124:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2124b
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
2125:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2125b
	sub x6, x6, #1
	cbnz x6, 2116b
	b 2115f
2114:
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2126:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2126b
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
2127:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2128:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2128b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x11
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
2129:
	mov v20.d[0], x19
	mov v20.d[1], x20
	mov v21.d[0], x21
	mov v21.d[1], x22
	mov v22.d[0], x23
	mov v22.d[1], x24
	mov v23.d[0], x25
	mov v23.d[1], x26
	mov v24.d[0], x27
	mov v24.d[1], x28
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
	umov x6, v17.d[0]
	umov x7, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	lsr x19, x6, #63
	sub x19, x13, x19
	lsr x20, x7, #63
	sub x20, x13, x20
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x26, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x26, x26, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x26, x26, x13
	sbc x13, x21, x22
	mul x27, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x27, x27, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x27, x27, x25
	sbc x25, x21, x22
	add x14, x12, #0
2130:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x1, x1, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	mul x24, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x24, x24, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	extr x22, x1, x26, #59
	str x22, [x16, #0]
	add x26, x1, #0
	extr x22, x24, x27, #59
	str x22, [x17, #0]
	add x27, x24, #0
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	extr x22, x13, x26, #59
	str x22, [x16, #0]
	extr x22, x25, x27, #59
	str x22, [x17, #0]
	umov x28, v18.d[1]
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
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	sub x14, x12, #1
	mov v25.d[0], x30
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x22, x4, x2
	madd x22, x5, x3, x22
	mul x26, x22, x28
	mul x22, x6, x2
	madd x22, x7, x3, x22
	mul x27, x22, x28
	movz x28, #0, lsl #0
	movz x23, #0, lsl #0
	movz x30, #0, lsl #0
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	cbz x14, 2131f
2133:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	str x1, [x16, #0]
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2133b
	b 2132f
2131:
2132:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	adds x1, x1, x23
	adc x13, x13, x28
	str x1, [x16, #0]
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	adds x24, x24, x30
	adc x25, x25, x28
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	str x13, [x16, #0]
	str x25, [x17, #0]
	umov x30, v25.d[0]
	umov x19, v20.d[0]
	umov x20, v20.d[1]
	umov x21, v21.d[0]
	umov x22, v21.d[1]
	umov x23, v22.d[0]
	umov x24, v22.d[1]
	umov x25, v23.d[0]
	umov x26, v23.d[1]
	umov x27, v24.d[0]
	umov x28, v24.d[1]
	cbnz x15, 2129b
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
2134:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2134b
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
2135:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2135b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2136:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2136b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2137:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2137b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2138:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2139:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2139b
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
2140:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2141:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2141b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2142:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2143:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	sub x15, x15, #1
	cbnz x15, 2140b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
2115:
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
2144:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2145:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #248]
	and x15, x15, x3
	str x15, [x0, #248]
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
2146:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2146b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2147:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	b 289f
288:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2148:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #240]
	str x3, [x16, #0]
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
2149:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2150:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2150b
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
2151:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	lsl x6, x12, #6
2152:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
2153:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2154:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	movz x7, #0, lsl #0
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
2155:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2155b
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
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2156:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2156b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
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
	cbnz x6, 2152b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2157:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2157b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2158:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2158b
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
2159:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2160:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2160b
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
2161:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2161b
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
2162:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsr x3, x12, #21
	cbz x3, 2163f
	lsl x6, x12, #7
2165:
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
2166:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2166b
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
2167:
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
	cbnz x14, 2167b
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
2168:
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
	cbnz x14, 2168b
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
2169:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2169b
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
2170:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2170b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x14, x12, #0
	adds x3, x7, x7
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
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
2171:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2171b
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2172:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2172b
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
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2173:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2173b
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
2174:
	ldr x3, [x16, #0]
	ldr x4, [x16, #8]
	extr x3, x4, x3, #1
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2174b
	sub x6, x6, #1
	cbnz x6, 2165b
	b 2164f
2163:
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
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2175:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2175b
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
2176:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2177:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2177b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x11
	add x3, x3, x3
	add x3, x3, x11
	add x3, x3, x3
	add x3, x3, x11
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
2178:
	mov v20.d[0], x19
	mov v20.d[1], x20
	mov v21.d[0], x21
	mov v21.d[1], x22
	mov v22.d[0], x23
	mov v22.d[1], x24
	mov v23.d[0], x25
	mov v23.d[1], x26
	mov v24.d[0], x27
	mov v24.d[1], x28
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
	umov x6, v17.d[0]
	umov x7, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	lsr x19, x6, #63
	sub x19, x13, x19
	lsr x20, x7, #63
	sub x20, x13, x20
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x26, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x26, x26, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x26, x26, x13
	sbc x13, x21, x22
	mul x27, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x27, x27, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x27, x27, x25
	sbc x25, x21, x22
	add x14, x12, #0
2179:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x1, x1, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	mul x24, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x24, x24, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	extr x22, x1, x26, #59
	str x22, [x16, #0]
	add x26, x1, #0
	extr x22, x24, x27, #59
	str x22, [x17, #0]
	add x27, x24, #0
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	extr x22, x13, x26, #59
	str x22, [x16, #0]
	extr x22, x25, x27, #59
	str x22, [x17, #0]
	umov x28, v18.d[1]
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
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	sub x14, x12, #1
	mov v25.d[0], x30
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x22, x4, x2
	madd x22, x5, x3, x22
	mul x26, x22, x28
	mul x22, x6, x2
	madd x22, x7, x3, x22
	mul x27, x22, x28
	movz x28, #0, lsl #0
	movz x23, #0, lsl #0
	movz x30, #0, lsl #0
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	cbz x14, 2180f
2182:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	str x1, [x16, #0]
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2182b
	b 2181f
2180:
2181:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	adds x1, x1, x23
	adc x13, x13, x28
	str x1, [x16, #0]
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	adds x24, x24, x30
	adc x25, x25, x28
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	str x13, [x16, #0]
	str x25, [x17, #0]
	umov x30, v25.d[0]
	umov x19, v20.d[0]
	umov x20, v20.d[1]
	umov x21, v21.d[0]
	umov x22, v21.d[1]
	umov x23, v22.d[0]
	umov x24, v22.d[1]
	umov x25, v23.d[0]
	umov x26, v23.d[1]
	umov x27, v24.d[0]
	umov x28, v24.d[1]
	cbnz x15, 2178b
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
2183:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2183b
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
2184:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2184b
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
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
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
2185:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2185b
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
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
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
2186:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2186b
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
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
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
2187:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2187b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2188:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2188b
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
2189:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
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
2190:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2190b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2191:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2191b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2192:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2192b
	sub x15, x15, #1
	cbnz x15, 2189b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
2164:
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
2193:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2193b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #2, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2194:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2194b
	sub x4, x7, #1
	csel x15, x4, x7, hs
	str x15, [x0, #248]
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
2195:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2195b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2196:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2196b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #248]
	and x15, x15, x3
	str x15, [x0, #248]
	ldr x3, [x0, #240]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	ldr x1, [x0, #240]
	ldr x3, [x16, #0]
	sub x1, x1, x3
	ldr x3, [x17, #0]
	mul x3, x3, x1
	add x3, x3, #1
	mul x10, x3, x4
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
2197:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2197b
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
	str x10, [x8, #0]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2198:
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
	cbnz x14, 2198b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
289:
	b 287f
286:
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
2199:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2199b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
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
2200:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2200b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x4, x7, hs
	str x15, [x0, #248]
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
2201:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2201b
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
	movz x3, #1, lsl #0
	str x3, [x16, #0]
287:
	b 285f
284:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
285:
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
2202:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2202b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	lsr x3, x12, #1
	lsl x3, x3, #3
	add x16, x16, x3
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2203:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2203b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #248]
	and x15, x15, x3
	cbnz x15, 2204f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2206:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2206b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2207:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2207b
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
2208:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2208b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #3, lsl #0
	str x3, [x16, #0]
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2209:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2209b
	sub x4, x7, #1
	csel x15, x7, x4, hs
	add x10, x15, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x3, #1
	orr x15, x15, x10
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
2210:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2210b
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
2211:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2211b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x14, x12, #0
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
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
2212:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2212b
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
2213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2213b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2214:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2214b
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
2215:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2215b
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
2216:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2216b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	lsr x12, x12, #1
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x0
	add x5, x5, #256
2217:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2217b
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
2218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2218b
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2219:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2219b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #1, lsl #0
	str x3, [x16, #0]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x11
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
2220:
	mov v20.d[0], x19
	mov v20.d[1], x20
	mov v21.d[0], x21
	mov v21.d[1], x22
	mov v22.d[0], x23
	mov v22.d[1], x24
	mov v23.d[0], x25
	mov v23.d[1], x26
	mov v24.d[0], x27
	mov v24.d[1], x28
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
	umov x6, v17.d[0]
	umov x7, v17.d[1]
	movz x13, #0, lsl #0
	lsr x9, x4, #63
	sub x9, x13, x9
	lsr x10, x5, #63
	sub x10, x13, x10
	lsr x19, x6, #63
	sub x19, x13, x19
	lsr x20, x7, #63
	sub x20, x13, x20
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x26, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x26, x26, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x26, x26, x13
	sbc x13, x21, x22
	mul x27, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x27, x27, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x27, x27, x25
	sbc x25, x21, x22
	add x14, x12, #0
2221:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	umulh x21, x4, x2
	and x22, x2, x9
	sub x21, x21, x22
	umulh x23, x5, x3
	and x22, x3, x10
	sub x23, x23, x22
	mul x22, x5, x3
	adds x1, x1, x22
	adc x21, x21, x23
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	mul x24, x6, x2
	umulh x21, x6, x2
	and x22, x2, x19
	sub x21, x21, x22
	umulh x23, x7, x3
	and x22, x3, x20
	sub x23, x23, x22
	mul x22, x7, x3
	adds x24, x24, x22
	adc x21, x21, x23
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	extr x22, x1, x26, #59
	str x22, [x16, #0]
	add x26, x1, #0
	extr x22, x24, x27, #59
	str x22, [x17, #0]
	add x27, x24, #0
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	extr x22, x13, x26, #59
	str x22, [x16, #0]
	extr x22, x25, x27, #59
	str x22, [x17, #0]
	umov x28, v18.d[1]
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
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	sub x14, x12, #1
	mov v25.d[0], x30
	ldr x2, [x16, #0]
	ldr x3, [x17, #0]
	mul x22, x4, x2
	madd x22, x5, x3, x22
	mul x26, x22, x28
	mul x22, x6, x2
	madd x22, x7, x3, x22
	mul x27, x22, x28
	movz x28, #0, lsl #0
	movz x23, #0, lsl #0
	movz x30, #0, lsl #0
	movz x13, #0, lsl #0
	movz x25, #0, lsl #0
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #0]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	cbz x14, 2222f
2224:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x26, x22
	mul x22, x26, x22
	adds x22, x22, x23
	adc x23, x21, x28
	adds x1, x1, x22
	adc x13, x13, x28
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	ldr x22, [x8, #8]
	umulh x21, x27, x22
	mul x22, x27, x22
	adds x22, x22, x30
	adc x30, x21, x28
	adds x24, x24, x22
	adc x25, x25, x28
	str x1, [x16, #0]
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2224b
	b 2223f
2222:
2223:
	ldr x2, [x16, #8]
	ldr x3, [x17, #8]
	mul x1, x4, x2
	mul x22, x5, x3
	adds x1, x1, x22
	umulh x21, x4, x2
	umulh x22, x5, x3
	adc x21, x21, x22
	and x22, x2, x9
	sub x21, x21, x22
	and x22, x3, x10
	sub x21, x21, x22
	lsr x22, x13, #63
	sub x22, x22, #1
	adds x1, x1, x13
	sbc x13, x21, x22
	adds x1, x1, x23
	adc x13, x13, x28
	str x1, [x16, #0]
	mul x24, x6, x2
	mul x22, x7, x3
	adds x24, x24, x22
	umulh x21, x6, x2
	umulh x22, x7, x3
	adc x21, x21, x22
	and x22, x2, x19
	sub x21, x21, x22
	and x22, x3, x20
	sub x21, x21, x22
	lsr x22, x25, #63
	sub x22, x22, #1
	adds x24, x24, x25
	sbc x25, x21, x22
	adds x24, x24, x30
	adc x25, x25, x28
	str x24, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x4
	and x23, x23, x5
	sub x13, x13, x22
	sub x13, x13, x23
	lsr x22, x2, #63
	lsr x23, x3, #63
	movz x21, #0, lsl #0
	sub x22, x21, x22
	sub x23, x21, x23
	and x22, x22, x6
	and x23, x23, x7
	sub x25, x25, x22
	sub x25, x25, x23
	str x13, [x16, #0]
	str x25, [x17, #0]
	umov x30, v25.d[0]
	umov x19, v20.d[0]
	umov x20, v20.d[1]
	umov x21, v21.d[0]
	umov x22, v21.d[1]
	umov x23, v22.d[0]
	umov x24, v22.d[1]
	umov x25, v23.d[0]
	umov x26, v23.d[1]
	umov x27, v24.d[0]
	umov x28, v24.d[1]
	cbnz x15, 2220b
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
2225:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2225b
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
2226:
	ldr x3, [x16, #0]
	eor x3, x3, x15
	adcs x3, x3, x7
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2227:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2227b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2228:
	ldr x3, [x10, #0]
	and x3, x3, x15
	ldr x4, [x8, #0]
	adcs x3, x3, x4
	str x3, [x5, #0]
	add x10, x10, #8
	add x8, x8, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2228b
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
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2230:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2230b
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
2231:
	add x5, x11, #0
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x5
	add x5, x5, x11
	add x5, x5, x0
	add x5, x5, #256
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
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
2232:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2232b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2233:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2233b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2234:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2234b
	sub x15, x15, #1
	cbnz x15, 2231b
	umov x1, v19.d[0]
	umov x2, v19.d[1]
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	lsl x3, x12, #3
	add x8, x8, x3
	lsr x13, x11, #3
	sub x13, x13, #2
	sub x13, x13, x12
	add x3, x12, #0
	add x12, x13, #0
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2235:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2235b
	add x12, x3, #0
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	lsl x3, x12, #3
	add x8, x8, x3
	lsr x13, x11, #3
	sub x13, x13, #2
	sub x13, x13, x12
	add x3, x12, #0
	add x12, x13, #0
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2236:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2236b
	add x12, x3, #0
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
2237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2237b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
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
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2238:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2238b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #248]
	and x15, x15, x3
	str x15, [x0, #248]
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
2239:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2239b
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
2240:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2240b
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
2241:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2241b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #0, lsl #0
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
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
2242:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2242b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
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
	movz x4, #1, lsl #0
	and x4, x15, x4
	orr x3, x3, x4
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
2243:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2243b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2244:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2244b
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
2245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2245b
	lsl x6, x12, #6
2246:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2247:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2247b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2248:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2248b
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
2249:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2249b
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
2250:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2250b
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
	cbnz x6, 2246b
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
2251:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2251b
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
2252:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2252b
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
2253:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2253b
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
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2254:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
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
2255:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2255b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	movz x3, #0, lsl #0
	str x3, [x16, #0]
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
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
2256:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2256b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
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
	movz x4, #1, lsl #0
	and x4, x15, x4
	orr x3, x3, x4
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
2257:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2257b
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
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2258:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2258b
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
2259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2259b
	lsl x6, x12, #6
2260:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2261:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2261b
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2262:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2262b
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
2263:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2263b
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
2264:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2264b
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
	cbnz x6, 2260b
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
2265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2265b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x0
	add x9, x9, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	add x16, x0, #256
	add x11, x16, #0
	lsr x12, x12, #1
	add x13, x12, #0
	movz x7, #0, lsl #0
2266:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2267:
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
	cbnz x14, 2267b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x8, x8, #8
	sub x13, x13, #1
	cbnz x13, 2266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x3, x12, #3
	add x16, x16, x3
	sub x16, x16, #8
	ldr x3, [x16, #0]
	lsr x3, x3, #63
	movz x7, #0, lsl #0
	sub x10, x7, x3
	ldr x3, [x0, #248]
	and x10, x10, x3
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	movz x7, #0, lsl #0
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	and x10, x10, x15
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
	and x10, x10, x15
	ldr x3, [x0, #240]
	movz x4, #1, lsl #0
	and x3, x3, x4
	sub x15, x7, x3
	and x10, x10, x15
	ldr x3, [x0, #240]
	movz x4, #3, lsl #0
	subs x3, x3, x4
	sub x4, x7, #1
	csel x15, x4, x7, hs
	and x10, x10, x15
	ldr x3, [x0, #240]
	lsr x3, x3, #33
	movz x4, #1, lsl #0
	subs x3, x3, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	and x10, x10, x15
	str x10, [x0, #248]
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
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2268:
	and x5, x2, x6
	cbz x5, 2269f
	b 2270f
2269:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2270:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2268b
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
	ldr x1, [x0, #136]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2271:
	and x5, x2, x6
	cbz x5, 2272f
	b 2273f
2272:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2273:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2271b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2274:
	and x5, x2, x6
	cbz x5, 2275f
	b 2276f
2275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2274b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2277:
	and x5, x2, x6
	cbz x5, 2278f
	b 2279f
2278:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2279:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2277b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #200]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2280:
	and x5, x2, x6
	cbz x5, 2281f
	b 2282f
2281:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2282:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2280b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #208]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2283:
	and x5, x2, x6
	cbz x5, 2284f
	b 2285f
2284:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2285:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2283b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #216]
	ldr x9, [x0, #184]
	add x1, x1, x9
	ldr x15, [x0, #248]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2286:
	and x5, x2, x6
	cbz x5, 2287f
	b 2288f
2287:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2288:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2286b
	ldr x3, [x0, #248]
	movz x4, #1, lsl #0
	and x0, x3, x4
	b 2205f
2204:
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2289:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2289b
	ldr x1, [x0, #136]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
2290:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2290b
	ldr x1, [x0, #168]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2291:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2291b
	ldr x1, [x0, #192]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2292:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2292b
	ldr x1, [x0, #200]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2293:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2293b
	ldr x1, [x0, #208]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2294:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2294b
	ldr x1, [x0, #216]
	ldr x2, [x0, #184]
	movz x3, #0, lsl #0
2295:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2295b
	movz x0, #2, lsl #0
2205:
	ret
	.p2align 6
