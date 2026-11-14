// The functions of `src/internal/vg_ffdh_generate_key_cached.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
