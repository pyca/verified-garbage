// The functions of `src/dsa.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_random:
	sub sp, sp, #256
	add x15, sp, #40
	str x0, [x15, #0]
	add x15, sp, #48
	str x1, [x15, #0]
	add x15, sp, #56
	str x2, [x15, #0]
	add x15, sp, #64
	str x3, [x15, #0]
	add x15, sp, #72
	str x4, [x15, #0]
	add x15, sp, #80
	str x5, [x15, #0]
	add x15, sp, #88
	str x6, [x15, #0]
	add x15, sp, #96
	str x7, [x15, #0]
	add x15, sp, #232
	str x30, [x15, #0]
	add x4, x3, x5
	add x15, sp, #168
	str x4, [x15, #0]
	movz x0, #0, lsl #0
	add x15, sp, #144
	str x0, [x15, #0]
	movz x0, #8, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	ldr x0, [sp, #256]
	add x15, sp, #104
	str x0, [x15, #0]
	ldr x0, [sp, #264]
	add x15, sp, #112
	str x0, [x15, #0]
	ldr x0, [sp, #272]
	add x15, sp, #120
	str x0, [x15, #0]
	ldr x0, [sp, #280]
	add x15, sp, #128
	str x0, [x15, #0]
	ldr x0, [sp, #288]
	add x15, sp, #136
	str x0, [x15, #0]
	movz x0, #0, lsl #0
	add x15, sp, #200
	str x0, [x15, #0]
	add x15, sp, #208
	str x0, [x15, #0]
	add x15, sp, #216
	str x0, [x15, #0]
	add x15, sp, #224
	str x0, [x15, #0]
	ldr x12, [sp, #168]
	ldr x9, [sp, #88]
	add x1, x12, #0
	add x13, x9, #0
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
	sub x13, x13, x8
	add x12, x12, x13
	add x9, x8, #0
	add x0, x10, #0
	add x15, sp, #168
	str x12, [x15, #0]
	add x15, sp, #176
	str x9, [x15, #0]
	add x10, x0, #0
	movz x8, #255, lsl #0
	movz x4, #127, lsl #0
	movz x3, #128, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #63, lsl #0
	movz x3, #64, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #31, lsl #0
	movz x3, #32, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #15, lsl #0
	movz x3, #16, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #7, lsl #0
	movz x3, #8, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #3, lsl #0
	movz x3, #4, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #1, lsl #0
	movz x3, #2, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	add x15, sp, #184
	str x8, [x15, #0]
	movz x0, #0, lsl #0
	movz x4, #1, lsl #0
	movz x3, #2, lsl #0
	subs x3, x9, x3
	csel x0, x4, x0, hs
	movz x3, #2, lsl #0
	subs x3, x10, x3
	csel x0, x4, x0, hs
	cbz x0, 25f
27:
	movz x0, #128, lsl #0
	add x15, sp, #160
	str x0, [x15, #0]
	movz x0, #4, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
28:
	ldr x0, [sp, #120]
	ldr x4, [sp, #144]
	sub x0, x0, x4
	ldr x4, [sp, #176]
	subs x3, x0, x4
	movz x0, #0, lsl #0
	movz x4, #1, lsl #0
	csel x3, x0, x4, hs
	cbnz x3, 29f
	ldr x12, [sp, #112]
	ldr x4, [sp, #144]
	add x12, x12, x4
	ldr x9, [sp, #176]
	add x2, sp, #200
	ldr x4, [sp, #88]
	add x2, x2, x4
	sub x2, x2, x9
	ldrb w0, [x12, #0]
	ldr x4, [sp, #184]
	and x0, x0, x4
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 211f
	b 212f
211:
213:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 213b
212:
	ldr x0, [sp, #144]
	ldr x4, [sp, #176]
	add x0, x0, x4
	add x15, sp, #144
	str x0, [x15, #0]
	add x2, sp, #200
	ldr x4, [sp, #88]
	add x2, x2, x4
	ldr x12, [sp, #168]
	ldr x9, [sp, #176]
	add x12, x12, x9
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
214:
	sub x2, x2, #1
	sub x12, x12, #1
	ldrb w0, [x2, #0]
	orr x10, x10, x0
	ldrb w4, [x12, #0]
	add x4, x4, x8
	sub x0, x0, x4
	lsr x0, x0, #63
	add x8, x0, #0
	sub x9, x9, #1
	cbnz x9, 214b
	movz x0, #0, lsl #0
	tst x10, x10
	csel x8, x0, x8, eq
	cbnz x8, 215f
	ldr x0, [sp, #160]
	sub x0, x0, #1
	add x15, sp, #160
	str x0, [x15, #0]
	cbz x0, 217f
	b 218f
217:
	add x15, sp, #192
	str x0, [x15, #0]
218:
	b 216f
215:
	movz x0, #1, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
216:
	b 210f
29:
	movz x0, #2, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
210:
	ldr x0, [sp, #192]
	sub x4, x0, #4
	cbz x4, 28b
	ldr x0, [sp, #192]
	sub x4, x0, #1
	cbz x4, 219f
	b 220f
219:
	ldr x0, [sp, #104]
	add x15, sp, #0
	str x0, [x15, #0]
	ldr x0, [sp, #128]
	add x15, sp, #8
	str x0, [x15, #0]
	ldr x0, [sp, #136]
	add x15, sp, #16
	str x0, [x15, #0]
	ldr x0, [sp, #40]
	ldr x1, [sp, #48]
	ldr x2, [sp, #64]
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	add x5, sp, #200
	ldr x6, [sp, #88]
	ldr x7, [sp, #96]
	bl {vg_dsa_sign}
	ldr x30, [sp, #232]
	orr w0, w0, w0
	add x15, sp, #192
	str x0, [x15, #0]
	cbz x0, 221f
	b 222f
221:
	ldr x0, [sp, #152]
	sub x0, x0, #1
	add x15, sp, #152
	str x0, [x15, #0]
	cbnz x0, 223f
	b 224f
223:
	movz x0, #4, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
224:
222:
220:
	ldr x0, [sp, #192]
	sub x4, x0, #4
	cbz x4, 27b
	b 26f
25:
	add x15, sp, #192
	str x0, [x15, #0]
26:
	ldr x0, [sp, #192]
	sub x4, x0, #1
	cbnz x4, 225f
	b 226f
225:
	ldr x12, [sp, #40]
	ldr x9, [sp, #48]
	movz x0, #0, lsl #0
227:
	strb w0, [x12, #0]
	add x12, x12, #1
	sub x9, x9, #1
	cbnz x9, 227b
226:
	movz x0, #0, lsl #0
	add x15, sp, #200
	str x0, [x15, #0]
	add x15, sp, #208
	str x0, [x15, #0]
	add x15, sp, #216
	str x0, [x15, #0]
	add x15, sp, #224
	str x0, [x15, #0]
	ldr x2, [sp, #56]
	ldr x0, [sp, #144]
	str x0, [x2, #0]
	ldr x0, [sp, #192]
	add sp, sp, #256
	ret
	.p2align 6

vg_dsa_verify:
	ldr x11, [sp, #0]
	movz x12, #0, lsl #0
	str x12, [x11, #320]
	str x12, [x11, #304]
	str x0, [x11, #256]
	str x2, [x11, #328]
	str x3, [x11, #336]
	str x4, [x11, #296]
	str x6, [x11, #312]
	str x7, [x11, #344]
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
250:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 250b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
252:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
253:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 253b
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
254:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
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
	cbz x6, 256f
258:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 258b
	b 257f
256:
257:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
260:
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
261:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 260b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
264:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 264b
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
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
266:
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
267:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
269:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 266b
244:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
270:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
272:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 273f
275:
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
276:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 276b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
277:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 277b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
278:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 275b
	b 274f
273:
274:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
279:
	and x5, x2, x6
	cbz x5, 280f
	b 281f
280:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
281:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 279b
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
282:
	ldrb w3, [x1, #0]
	orr x8, x8, x3
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 282b
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
283:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
284:
	and x5, x2, x6
	cbz x5, 285f
	b 286f
285:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
286:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 284b
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
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 288f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 290f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
292:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
293:
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
	cbnz x13, 293b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
294:
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
295:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 295b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
297:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
298:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
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
299:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 294b
	b 291f
290:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2101f
2103:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2103b
	b 2102f
2101:
2102:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2104:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2105:
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
2106:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2105b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2109:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2109b
291:
	b 289f
288:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2111:
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
2112:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2111b
289:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2115:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2116:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2117f
	b 2118f
2117:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2118:
	cbnz x2, 2116b
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
2119:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2119b
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
2120:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2120b
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
2121:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2122:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2123:
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
2124:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2123b
2125:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2126:
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
	cbz x3, 2127f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2129:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2128f
2127:
2128:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2126b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2125b
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
2130:
	and x5, x2, x6
	cbz x5, 2131f
	b 2132f
2131:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2132:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2130b
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
2133:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2133b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2134:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2135f
	b 2136f
2135:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2136:
	cbnz x2, 2134b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2137:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #280]
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
2138:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2139f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2141f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2143:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2144:
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
	cbnz x13, 2144b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2145:
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
2146:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2146b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
2148:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2149:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2149b
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
2150:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2151:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2145b
	b 2142f
2141:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
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
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2155:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2156:
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2156b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2160:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2160b
2142:
	b 2140f
2139:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2161:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2162:
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
2163:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2162b
2140:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2166:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2167:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2168f
	b 2169f
2168:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2169:
	cbnz x2, 2167b
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
2170:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2170b
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
2171:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2171b
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
2172:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2172b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2173:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2174:
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
2175:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2175b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2174b
2176:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2177:
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
	cbz x3, 2178f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2180:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2180b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2179f
2178:
2179:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2177b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2176b
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
2181:
	and x5, x2, x6
	cbz x5, 2182f
	b 2183f
2182:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2183:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2181b
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
2184:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2184b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2185:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2186f
	b 2187f
2186:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2187:
	cbnz x2, 2185b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2188:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2188b
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #296]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x4, #13312, lsl #0
	add x0, x0, x4
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
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2190:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2191f
	b 2192f
2191:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2192:
	cbnz x2, 2190b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2193:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2193b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2194:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2194b
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
	ldr x3, [x0, #296]
	ldr x4, [x0, #336]
	add x3, x3, x4
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x4, #13312, lsl #0
	add x0, x0, x4
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2195:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2195b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2196:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2197f
	b 2198f
2197:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2198:
	cbnz x2, 2196b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2199:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2199b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2200:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2200b
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
	ldr x3, [x0, #296]
	ldr x4, [x0, #336]
	add x3, x3, x4
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14912, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #14784, lsl #0
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
2201:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2201b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2202f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2204f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2206:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2206b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2207:
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
	cbnz x13, 2207b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2208:
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
2209:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2209b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
2211:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2211b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2212:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2212b
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
2213:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2213b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2214:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2214b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2208b
	b 2205f
2204:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2215f
2217:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2217b
	b 2216f
2215:
2216:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2218:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2218b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2219:
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
2220:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2220b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2221:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2219b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2223:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2223b
2205:
	b 2203f
2202:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2224:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2224b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2225:
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
2226:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2228:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2225b
2203:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2229:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2230:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2231f
	b 2232f
2231:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2232:
	cbnz x2, 2230b
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
2233:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2233b
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
2234:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2234b
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
2235:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2235b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2236:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2236b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2237:
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
2238:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2238b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2237b
2239:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2240:
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
2241:
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
2242:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2242b
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
	cbnz x4, 2241b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2240b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2239b
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
2243:
	and x5, x2, x6
	cbz x5, 2244f
	b 2245f
2244:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2245:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2243b
	ldr x0, [x0, #128]
	ldr x3, [x0, #312]
	str x3, [x0, #128]
	ldr x3, [x0, #352]
	str x3, [x0, #136]
	movz x3, #14880, lsl #0
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
2246:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2246b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2247f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2249f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2251:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2251b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2252:
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
	cbnz x13, 2252b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2253:
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
2254:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2255:
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
	cbnz x14, 2255b
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
2256:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2256b
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
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2258:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2258b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2259:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2259b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2253b
	b 2250f
2249:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2260f
2262:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2262b
	b 2261f
2260:
2261:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2263:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2263b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2264:
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
2265:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2265b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2266:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2266b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2267:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2267b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2264b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2268:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2268b
2250:
	b 2248f
2247:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2269:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2269b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2270:
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
2271:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2271b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2272b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2273:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2273b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2270b
2248:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2274:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2274b
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
2275:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2275b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2276:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2276b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2277f
2279:
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
2280:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2280b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2281:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2281b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2282:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2282b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2279b
	b 2278f
2277:
2278:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
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
	ldr x0, [x0, #128]
	movz x3, #14880, lsl #0
	add x3, x0, x3
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14784, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
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
2286:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2286b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2287f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2289f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2291:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2291b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2292:
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
	cbnz x13, 2292b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2293:
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
2294:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2294b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2295:
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
	cbnz x14, 2295b
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
2296:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2296b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2297:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2297b
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
2298:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2298b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2299:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2299b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2293b
	b 2290f
2289:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2300f
2302:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2302b
	b 2301f
2300:
2301:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2303:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2303b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2304:
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2304b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2308:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2308b
2290:
	b 2288f
2287:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2309:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2309b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2310:
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
2311:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2311b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2312:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2312b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2313:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2313b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2310b
2288:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2314:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2314b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2315:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2316f
	b 2317f
2316:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2317:
	cbnz x2, 2315b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2318:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2318b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2319:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2320f
	b 2321f
2320:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2321:
	cbnz x2, 2319b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
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
2322:
	and x5, x2, x6
	cbz x5, 2323f
	b 2324f
2323:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2324:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2322b
	ldr x0, [x0, #128]
	ldr x3, [x0, #296]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14784, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #14848, lsl #0
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
2325:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2325b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2326f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2328f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2330:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2330b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2331:
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
	cbnz x13, 2331b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2332:
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
2333:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2333b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2334:
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
	cbnz x14, 2334b
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
2335:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2335b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2336:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2336b
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
2337:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2337b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2338:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2338b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2332b
	b 2329f
2328:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2339f
2341:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2341b
	b 2340f
2339:
2340:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2342:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2342b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2343:
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
2344:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2344b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2345:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2345b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2346:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2346b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2343b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2347:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2347b
2329:
	b 2327f
2326:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2348:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2348b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2349:
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
2350:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2350b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2351:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2351b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2352:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2352b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2349b
2327:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2353:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2353b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2354:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2355f
	b 2356f
2355:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2356:
	cbnz x2, 2354b
	ldr x8, [x0, #104]
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
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2358:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2359f
	b 2360f
2359:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2360:
	cbnz x2, 2358b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
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
2361:
	and x5, x2, x6
	cbz x5, 2362f
	b 2363f
2362:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2363:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2361b
	ldr x0, [x0, #128]
	ldr x3, [x0, #272]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	ldr x3, [x0, #280]
	str x3, [x0, #144]
	ldr x3, [x0, #328]
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
2364:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2364b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2365f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2367f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2369:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2369b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2370:
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
	cbnz x13, 2370b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2371:
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
2372:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2372b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2373:
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
	cbnz x14, 2373b
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
2374:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2374b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2375:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2375b
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
2376:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2376b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2377:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2377b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2371b
	b 2368f
2367:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2378f
2380:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2380b
	b 2379f
2378:
2379:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2381:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2381b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2382:
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
2383:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2383b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2384:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2384b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2385:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2385b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2382b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2386:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2386b
2368:
	b 2366f
2365:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2387:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2387b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2388:
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
2389:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2389b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2390:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2390b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2391:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2391b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2388b
2366:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2392:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2392b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2393:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2394f
	b 2395f
2394:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2395:
	cbnz x2, 2393b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2396:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2396b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2397:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2398f
	b 2399f
2398:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2399:
	cbnz x2, 2397b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2400:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2400b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	add x14, x12, #0
2401:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2401b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #72]
	add x14, x12, #0
2402:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2402b
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
2403:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2403b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2404:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2404b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2405:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2405b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2406:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2406b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2407:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2407b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2408:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2408b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2409:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2409b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2410:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2410b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2411:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2411b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2412:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2412b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2413:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2413b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
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
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2415:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2415b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2416:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2416b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2417:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2417b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2418:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2418b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2419:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2419b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2420:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2420b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2421:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2421b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2422:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2422b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	add x14, x12, #0
2423:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2423b
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2424:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2424b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x5, [x0, #128]
	ldr x3, [x5, #336]
	str x3, [x0, #144]
	movz x4, #14816, lsl #0
	add x4, x5, x4
	str x4, [x0, #136]
	movz x4, #14848, lsl #0
	add x4, x5, x4
	str x4, [x0, #176]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
2425:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldr x5, [x0, #176]
	add x5, x5, x4
	ldrb w3, [x3, #0]
	ldrb w5, [x5, #0]
	lsl x3, x3, #8
	add x3, x3, x5
	str x3, [x0, #168]
	movz x3, #4, lsl #0
	str x3, [x0, #160]
2426:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #168]
	lsl x4, x3, #2
	str x4, [x0, #168]
	lsr x4, x3, #14
	movz x5, #3, lsl #0
	and x4, x4, x5
	lsl x4, x4, #2
	lsr x3, x3, #6
	and x3, x3, x5
	add x3, x4, x3
	str x3, [x0, #216]
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2427:
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
2428:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2428b
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
	cbnz x4, 2427b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2426b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2425b
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
2429:
	and x5, x2, x6
	cbz x5, 2430f
	b 2431f
2430:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2431:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2429b
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
2432:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2432b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2433f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2435f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2437:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2437b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2438:
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
	cbnz x13, 2438b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2439:
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
2440:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2440b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2441:
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
	cbnz x14, 2441b
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
2442:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2442b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2443:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2443b
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
2444:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2444b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2445:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2445b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2439b
	b 2436f
2435:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2446f
2448:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2448b
	b 2447f
2446:
2447:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2449:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2449b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2450:
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
2451:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2451b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2452:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2452b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2453:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2453b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2450b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2454:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2454b
2436:
	b 2434f
2433:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2455:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2455b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2456:
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
2457:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2457b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2458:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2458b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2459:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2459b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2456b
2434:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2460:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2460b
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
2461:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2461b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2462:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2462b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2463f
2465:
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
2466:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2466b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2467:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2467b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2468:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2468b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2465b
	b 2464f
2463:
2464:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2469:
	and x5, x2, x6
	cbz x5, 2470f
	b 2471f
2470:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2471:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2469b
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x3, [x0, #296]
	add x2, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
2472:
	ldrb w3, [x1, #0]
	ldrb w10, [x2, #0]
	eor x3, x3, x10
	orr x8, x8, x3
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2472b
	tst x8, x8
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
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

vg_dsa_validate_public_key:
	add x11, x4, #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x12, #0, lsl #0
	str x12, [x11, #320]
	str x12, [x11, #304]
	str x0, [x11, #256]
	str x2, [x11, #328]
	str x3, [x11, #336]
	str x4, [x11, #296]
	str x6, [x11, #312]
	str x7, [x11, #344]
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
250:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 250b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
252:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
253:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 253b
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
254:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
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
	cbz x6, 256f
258:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 258b
	b 257f
256:
257:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
260:
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
261:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 260b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
264:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 264b
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
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
266:
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
267:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
269:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 266b
244:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
270:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
272:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 273f
275:
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
276:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 276b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
277:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 277b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
278:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 275b
	b 274f
273:
274:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
279:
	and x5, x2, x6
	cbz x5, 280f
	b 281f
280:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
281:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 279b
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
282:
	ldrb w3, [x1, #0]
	orr x8, x8, x3
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 282b
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
283:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
284:
	and x5, x2, x6
	cbz x5, 285f
	b 286f
285:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
286:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 284b
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
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 288f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 290f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
292:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
293:
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
	cbnz x13, 293b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
294:
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
295:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 295b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
297:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
298:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
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
299:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 294b
	b 291f
290:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2101f
2103:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2103b
	b 2102f
2101:
2102:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2104:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2105:
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
2106:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2105b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2109:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2109b
291:
	b 289f
288:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2111:
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
2112:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2111b
289:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2115:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2116:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2117f
	b 2118f
2117:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2118:
	cbnz x2, 2116b
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
2119:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2119b
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
2120:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2120b
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
2121:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2122:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2123:
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
2124:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2123b
2125:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2126:
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
	cbz x3, 2127f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2129:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2129b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2128f
2127:
2128:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2126b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2125b
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
2130:
	and x5, x2, x6
	cbz x5, 2131f
	b 2132f
2131:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2132:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2130b
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
2133:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2133b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2134:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2135f
	b 2136f
2135:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2136:
	cbnz x2, 2134b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2137:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x3, [x0, #280]
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
2138:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2139f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2141f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2143:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2144:
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
	cbnz x13, 2144b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2145:
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
2146:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2146b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
2148:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2149:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2149b
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
2150:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2151:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2145b
	b 2142f
2141:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
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
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2155:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2156:
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2156b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2160:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2160b
2142:
	b 2140f
2139:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2161:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2162:
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
2163:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2162b
2140:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2166:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2167:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2168f
	b 2169f
2168:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2169:
	cbnz x2, 2167b
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
2170:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2170b
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
2171:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2171b
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
2172:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2172b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2173:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2174:
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
2175:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2175b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2174b
2176:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2177:
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
	cbz x3, 2178f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2180:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2180b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2179f
2178:
2179:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2177b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2176b
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
2181:
	and x5, x2, x6
	cbz x5, 2182f
	b 2183f
2182:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2183:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2181b
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
2184:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2184b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2185:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2186f
	b 2187f
2186:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2187:
	cbnz x2, 2185b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2188:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2188b
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

vg_dsa_verify_prevalidated:
	ldr x11, [sp, #0]
	movz x12, #0, lsl #0
	str x12, [x11, #320]
	str x12, [x11, #304]
	str x0, [x11, #256]
	str x2, [x11, #328]
	str x3, [x11, #336]
	str x4, [x11, #296]
	str x6, [x11, #312]
	str x7, [x11, #344]
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
226:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 226b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
227:
	and x5, x2, x6
	cbz x5, 228f
	b 229f
228:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
229:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 227b
	ldr x0, [x0, #128]
	ldr x3, [x0, #296]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x4, #13312, lsl #0
	add x0, x0, x4
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
230:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 230b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
234:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
235:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 235b
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
	ldr x3, [x0, #296]
	ldr x4, [x0, #336]
	add x3, x3, x4
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x4, #13312, lsl #0
	add x0, x0, x4
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
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
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
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
240:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
241:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 241b
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
	ldr x3, [x0, #296]
	ldr x4, [x0, #336]
	add x3, x3, x4
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14912, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #14784, lsl #0
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
250:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 250b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
252:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
253:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 253b
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
254:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
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
	cbz x6, 256f
258:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 258b
	b 257f
256:
257:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
259:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 259b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
260:
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
261:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 260b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
264:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 264b
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
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
266:
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
267:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 267b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
269:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 266b
244:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
270:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
271:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 272f
	b 273f
272:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
273:
	cbnz x2, 271b
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
274:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 274b
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
275:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 275b
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
276:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
277:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 277b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
278:
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
279:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 278b
280:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
281:
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
282:
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
283:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
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
	cbnz x4, 282b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 281b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 280b
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
284:
	and x5, x2, x6
	cbz x5, 285f
	b 286f
285:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
286:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 284b
	ldr x0, [x0, #128]
	ldr x3, [x0, #312]
	str x3, [x0, #128]
	ldr x3, [x0, #352]
	str x3, [x0, #136]
	movz x3, #14880, lsl #0
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
287:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 287b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 288f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 290f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
292:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 292b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
293:
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
	cbnz x13, 293b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
294:
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
295:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 295b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
297:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
298:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
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
299:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2100:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 294b
	b 291f
290:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2101f
2103:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2103b
	b 2102f
2101:
2102:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2104:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2105:
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
2106:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2105b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2109:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2109b
291:
	b 289f
288:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2111:
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
2112:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2111b
289:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2115:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2115b
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
2116:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2117:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2118f
2120:
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
2121:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2122:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2123:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2123b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2120b
	b 2119f
2118:
2119:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2124:
	and x5, x2, x6
	cbz x5, 2125f
	b 2126f
2125:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2126:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2124b
	ldr x0, [x0, #128]
	movz x3, #14880, lsl #0
	add x3, x0, x3
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14784, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
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
2127:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2128f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2130f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2132:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2133:
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
	cbnz x13, 2133b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2134:
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
2135:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
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
2137:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2138:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2138b
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
2139:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2139b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2140:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2134b
	b 2131f
2130:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2141f
2143:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2143b
	b 2142f
2141:
2142:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2144:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2145:
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
2146:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2146b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2147:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2148:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2145b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2149:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2149b
2131:
	b 2129f
2128:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2150:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2151:
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
2152:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2153:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2154:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2151b
2129:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2155:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2156:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2157f
	b 2158f
2157:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2158:
	cbnz x2, 2156b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2159:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2160:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2161f
	b 2162f
2161:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2162:
	cbnz x2, 2160b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
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
2163:
	and x5, x2, x6
	cbz x5, 2164f
	b 2165f
2164:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2165:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2163b
	ldr x0, [x0, #128]
	ldr x3, [x0, #296]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x3, #14784, lsl #0
	add x3, x0, x3
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #14848, lsl #0
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
2166:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2166b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2167f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2169f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2171:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2171b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2172:
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
	cbnz x13, 2172b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2173:
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
2174:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2174b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2175:
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
	cbnz x14, 2175b
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
2176:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2177:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2177b
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
2178:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2178b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2179:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2173b
	b 2170f
2169:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2180f
2182:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2182b
	b 2181f
2180:
2181:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2183:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2183b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2184:
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
2185:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2185b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2186:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2186b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2187:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2187b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2184b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2188:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2188b
2170:
	b 2168f
2167:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2189:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2189b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2190:
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
2191:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2190b
2168:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2194:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2194b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2195:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2196f
	b 2197f
2196:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2197:
	cbnz x2, 2195b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2198:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2198b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2199:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2200f
	b 2201f
2200:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2201:
	cbnz x2, 2199b
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_5_1}
	umov x30, v31.d[0]
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
2202:
	and x5, x2, x6
	cbz x5, 2203f
	b 2204f
2203:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2204:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2202b
	ldr x0, [x0, #128]
	ldr x3, [x0, #272]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	ldr x3, [x0, #280]
	str x3, [x0, #144]
	ldr x3, [x0, #328]
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
2205:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2205b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2206f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2208f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2210:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2210b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2211:
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
	cbnz x13, 2211b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2212:
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
2213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2213b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2214:
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
	cbnz x14, 2214b
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
2215:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2215b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2216:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2216b
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
2217:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2218:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2218b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2212b
	b 2209f
2208:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2219f
2221:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2221b
	b 2220f
2219:
2220:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2222:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2223:
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
2224:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2224b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
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
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2226:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2223b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2227:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2227b
2209:
	b 2207f
2206:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2228:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2229:
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
2230:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2231:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2231b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2232:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2232b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2229b
2207:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2233:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2233b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2234:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2235f
	b 2236f
2235:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2236:
	cbnz x2, 2234b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2237:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2237b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
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
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_4_7}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_mul_5_5_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #96]
	add x14, x12, #0
2241:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2241b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	add x14, x12, #0
2242:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2242b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #72]
	add x14, x12, #0
2243:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2243b
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
2244:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2244b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2245:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2245b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2246:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2246b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2247:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2247b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2248b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2249:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2249b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2250:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2250b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2251:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2251b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2252:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2252b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2253:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2253b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2254:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2255b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2256:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2256b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2257:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2257b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2258:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2258b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2259:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2259b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2260b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2261:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2261b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2262:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2262b
	ldr x3, [x0, #208]
	ldr x4, [x0, #48]
	add x4, x4, #2
	lsl x4, x4, #3
	add x3, x3, x4
	str x3, [x0, #208]
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2263:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2263b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	add x14, x12, #0
2264:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2264b
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
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
	ldr x5, [x0, #128]
	ldr x3, [x5, #336]
	str x3, [x0, #144]
	movz x4, #14816, lsl #0
	add x4, x5, x4
	str x4, [x0, #136]
	movz x4, #14848, lsl #0
	add x4, x5, x4
	str x4, [x0, #176]
	movz x3, #0, lsl #0
	str x3, [x0, #152]
2266:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldr x5, [x0, #176]
	add x5, x5, x4
	ldrb w3, [x3, #0]
	ldrb w5, [x5, #0]
	lsl x3, x3, #8
	add x3, x3, x5
	str x3, [x0, #168]
	movz x3, #4, lsl #0
	str x3, [x0, #160]
2267:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x3, [x0, #168]
	lsl x4, x3, #2
	str x4, [x0, #168]
	lsr x4, x3, #14
	movz x5, #3, lsl #0
	and x4, x4, x5
	lsl x4, x4, #2
	lsr x3, x3, #6
	and x3, x3, x5
	add x3, x4, x3
	str x3, [x0, #216]
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2268:
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
2269:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2269b
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
	cbnz x4, 2268b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2267b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2266b
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
2270:
	and x5, x2, x6
	cbz x5, 2271f
	b 2272f
2271:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2272:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2270b
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
2273:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2273b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2274f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2276f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2278:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2278b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2279:
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
	cbnz x13, 2279b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2280:
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
2281:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2281b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2282:
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
	cbnz x14, 2282b
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
2283:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2283b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2284:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2284b
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
2285:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2285b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2286:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2286b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2280b
	b 2277f
2276:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2287f
2289:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2289b
	b 2288f
2287:
2288:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
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
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2291:
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
2292:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2292b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2293:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2293b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2294:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2294b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2291b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2295:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2295b
2277:
	b 2275f
2274:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
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
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2297:
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
2298:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2298b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2299:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2299b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2300:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2300b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2297b
2275:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2301:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2301b
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
2302:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2302b
	ldr x8, [x0, #72]
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
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2304f
2306:
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
2307:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2307b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2308:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2308b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2309:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2309b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2306b
	b 2305f
2304:
2305:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2310:
	and x5, x2, x6
	cbz x5, 2311f
	b 2312f
2311:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2312:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2310b
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x3, [x0, #296]
	add x2, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
2313:
	ldrb w3, [x1, #0]
	ldrb w10, [x2, #0]
	eor x3, x3, x10
	orr x8, x8, x3
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2313b
	tst x8, x8
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
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

vg_dsa_generate_key:
	sub sp, sp, #256
	add x15, sp, #40
	str x0, [x15, #0]
	add x15, sp, #48
	str x1, [x15, #0]
	add x15, sp, #56
	str x2, [x15, #0]
	add x15, sp, #64
	str x3, [x15, #0]
	add x15, sp, #72
	str x4, [x15, #0]
	add x15, sp, #80
	str x5, [x15, #0]
	add x15, sp, #88
	str x6, [x15, #0]
	add x15, sp, #112
	str x7, [x15, #0]
	add x15, sp, #232
	str x30, [x15, #0]
	add x4, x3, x5
	add x15, sp, #168
	str x4, [x15, #0]
	movz x0, #0, lsl #0
	add x15, sp, #144
	str x0, [x15, #0]
	add x15, sp, #192
	str x0, [x15, #0]
	ldr x0, [sp, #256]
	add x15, sp, #120
	str x0, [x15, #0]
	ldr x0, [sp, #264]
	add x15, sp, #128
	str x0, [x15, #0]
	ldr x0, [sp, #272]
	add x15, sp, #136
	str x0, [x15, #0]
	ldr x0, [sp, #64]
	ldr x1, [sp, #72]
	ldr x2, [sp, #80]
	ldr x3, [sp, #88]
	ldr x4, [sp, #128]
	ldr x5, [sp, #136]
	bl {vg_dsa_check_parameters}
	ldr x30, [sp, #232]
	orr w0, w0, w0
	cbz x0, 20f
	movz x0, #0, lsl #0
	add x15, sp, #200
	str x0, [x15, #0]
	add x15, sp, #208
	str x0, [x15, #0]
	add x15, sp, #216
	str x0, [x15, #0]
	add x15, sp, #224
	str x0, [x15, #0]
	ldr x12, [sp, #168]
	ldr x9, [sp, #88]
	add x1, x12, #0
	add x13, x9, #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
22:
	ldrb w3, [x1, #0]
	cbz x8, 23f
	b 24f
23:
	cbnz x3, 25f
	b 26f
25:
	add x8, x9, #0
	add x10, x3, #0
26:
24:
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 22b
	sub x13, x13, x8
	add x12, x12, x13
	add x9, x8, #0
	add x0, x10, #0
	add x15, sp, #168
	str x12, [x15, #0]
	add x15, sp, #176
	str x9, [x15, #0]
	add x10, x0, #0
	movz x8, #255, lsl #0
	movz x4, #127, lsl #0
	movz x3, #128, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #63, lsl #0
	movz x3, #64, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #31, lsl #0
	movz x3, #32, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #15, lsl #0
	movz x3, #16, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #7, lsl #0
	movz x3, #8, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #3, lsl #0
	movz x3, #4, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	movz x4, #1, lsl #0
	movz x3, #2, lsl #0
	subs x3, x0, x3
	csel x8, x8, x4, hs
	add x15, sp, #184
	str x8, [x15, #0]
	movz x0, #0, lsl #0
	movz x4, #1, lsl #0
	movz x3, #2, lsl #0
	subs x3, x9, x3
	csel x0, x4, x0, hs
	movz x3, #2, lsl #0
	subs x3, x10, x3
	csel x0, x4, x0, hs
	cbz x0, 27f
	movz x0, #128, lsl #0
	add x15, sp, #160
	str x0, [x15, #0]
	movz x0, #4, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
29:
	ldr x0, [sp, #120]
	ldr x4, [sp, #144]
	sub x0, x0, x4
	ldr x4, [sp, #176]
	subs x3, x0, x4
	movz x0, #0, lsl #0
	movz x4, #1, lsl #0
	csel x3, x0, x4, hs
	cbnz x3, 210f
	ldr x12, [sp, #112]
	ldr x4, [sp, #144]
	add x12, x12, x4
	ldr x9, [sp, #176]
	add x2, sp, #200
	ldr x4, [sp, #88]
	add x2, x2, x4
	sub x2, x2, x9
	ldrb w0, [x12, #0]
	ldr x4, [sp, #184]
	and x0, x0, x4
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 212f
	b 213f
212:
214:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 214b
213:
	ldr x0, [sp, #144]
	ldr x4, [sp, #176]
	add x0, x0, x4
	add x15, sp, #144
	str x0, [x15, #0]
	add x2, sp, #200
	ldr x4, [sp, #88]
	add x2, x2, x4
	ldr x12, [sp, #168]
	ldr x9, [sp, #176]
	add x12, x12, x9
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
215:
	sub x2, x2, #1
	sub x12, x12, #1
	ldrb w0, [x2, #0]
	orr x10, x10, x0
	ldrb w4, [x12, #0]
	add x4, x4, x8
	sub x0, x0, x4
	lsr x0, x0, #63
	add x8, x0, #0
	sub x9, x9, #1
	cbnz x9, 215b
	movz x0, #0, lsl #0
	tst x10, x10
	csel x8, x0, x8, eq
	cbnz x8, 216f
	ldr x0, [sp, #160]
	sub x0, x0, #1
	add x15, sp, #160
	str x0, [x15, #0]
	cbz x0, 218f
	b 219f
218:
	add x15, sp, #192
	str x0, [x15, #0]
219:
	b 217f
216:
	movz x0, #1, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
217:
	b 211f
210:
	movz x0, #2, lsl #0
	add x15, sp, #192
	str x0, [x15, #0]
211:
	ldr x0, [sp, #192]
	sub x4, x0, #4
	cbz x4, 29b
	ldr x0, [sp, #192]
	add x15, sp, #192
	str x0, [x15, #0]
	sub x4, x0, #1
	cbz x4, 220f
	b 221f
220:
	ldr x0, [sp, #136]
	add x15, sp, #0
	str x0, [x15, #0]
	ldr x0, [sp, #40]
	ldr x1, [sp, #48]
	ldr x2, [sp, #64]
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	add x5, sp, #200
	ldr x6, [sp, #88]
	ldr x7, [sp, #128]
	bl {vg_dsa_derive_key}
	ldr x30, [sp, #232]
	orr w0, w0, w0
	add x15, sp, #192
	str x0, [x15, #0]
221:
	b 28f
27:
	add x15, sp, #192
	str x0, [x15, #0]
28:
	b 21f
20:
21:
	ldr x0, [sp, #192]
	sub x4, x0, #1
	cbnz x4, 222f
	b 223f
222:
	ldr x12, [sp, #40]
	ldr x9, [sp, #48]
	movz x0, #0, lsl #0
224:
	strb w0, [x12, #0]
	add x12, x12, #1
	sub x9, x9, #1
	cbnz x9, 224b
223:
	movz x0, #0, lsl #0
	add x15, sp, #200
	str x0, [x15, #0]
	add x15, sp, #208
	str x0, [x15, #0]
	add x15, sp, #216
	str x0, [x15, #0]
	add x15, sp, #224
	str x0, [x15, #0]
	ldr x2, [sp, #56]
	ldr x0, [sp, #144]
	str x0, [x2, #0]
	ldr x0, [sp, #192]
	add sp, sp, #256
	ret
	.p2align 6

vg_dsa_derive_key:
	add x11, x7, #0
	movz x12, #0, lsl #0
	str x12, [x11, #296]
	str x12, [x11, #304]
	str x12, [x11, #312]
	str x12, [x11, #344]
	str x0, [x11, #320]
	str x2, [x11, #256]
	str x4, [x11, #328]
	str x6, [x11, #336]
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
	str x5, [x11, #288]
	movz x3, #15712, lsl #0
	add x3, x11, x3
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
	ldr x3, [x0, #288]
	str x3, [x0, #128]
	ldr x3, [x0, #336]
	str x3, [x0, #136]
	movz x4, #13312, lsl #0
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
	ldr x3, [x0, #272]
	str x3, [x0, #128]
	ldr x3, [x0, #328]
	str x3, [x0, #136]
	ldr x3, [x0, #288]
	str x3, [x0, #144]
	ldr x3, [x0, #336]
	str x3, [x0, #152]
	movz x3, #15328, lsl #0
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
232:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 232b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 233f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 235f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
237:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
238:
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
	cbnz x13, 238b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
239:
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
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
241:
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
	cbnz x14, 241b
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
242:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 242b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
243:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 243b
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
244:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 244b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
245:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 245b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 239b
	b 236f
235:
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
236:
	b 234f
233:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
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
	ldr x13, [x0, #48]
	lsl x13, x13, #7
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
234:
	ldr x8, [x0, #72]
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
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
264:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 264b
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
265:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 265b
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
266:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
268:
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
269:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 269b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 268b
270:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
271:
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
272:
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
273:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
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
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #16
	cbnz x4, 272b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 271b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 270b
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
274:
	and x5, x2, x6
	cbz x5, 275f
	b 276f
275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 274b
	ldr x0, [x0, #128]
	movz x3, #15328, lsl #0
	add x1, x0, x3
	movz x3, #15712, lsl #0
	add x2, x0, x3
	ldr x9, [x0, #328]
	movz x8, #0, lsl #0
	sub x8, x8, #1
277:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 277b
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
278:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
279:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 280f
	b 281f
280:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
281:
	cbnz x2, 279b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
282:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 282b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
283:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 283b
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
284:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 284b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
285:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 286f
	b 287f
286:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
287:
	cbnz x2, 285b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
288:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 288b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
289:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 289b
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
290:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
291:
	and x5, x2, x6
	cbz x5, 292f
	b 293f
292:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
293:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 291b
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
294:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 294b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 295f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 297f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
299:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2100:
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
	cbnz x13, 2100b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2101:
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
2102:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2103:
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
	cbnz x14, 2103b
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
2104:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2104b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2105:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2105b
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
2106:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2107:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2101b
	b 298f
297:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2108f
2110:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2110b
	b 2109f
2108:
2109:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2111:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2112:
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
2113:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2112b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2116:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2116b
298:
	b 296f
295:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2117:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2118:
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
2119:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2118b
296:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2122:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2122b
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
2123:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2123b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2124:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2125f
2127:
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
2128:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2128b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2127b
	b 2126f
2125:
2126:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2131:
	and x5, x2, x6
	cbz x5, 2132f
	b 2133f
2132:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2133:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2131b
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
2134:
	ldrb w3, [x1, #0]
	orr x8, x8, x3
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 2134b
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
2135:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2136:
	and x5, x2, x6
	cbz x5, 2137f
	b 2138f
2137:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2138:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2136b
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
2139:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2139b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2140f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2142f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2144:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2145:
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
	cbnz x13, 2145b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2146:
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
2147:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2148:
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
	cbnz x14, 2148b
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
2149:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2150:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2150b
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
2151:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2152:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2146b
	b 2143f
2142:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2153f
2155:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2155b
	b 2154f
2153:
2154:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2156:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2156b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2157:
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2157b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2161:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2161b
2143:
	b 2141f
2140:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2162:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2163:
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
2164:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2163b
2141:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2167:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2167b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2168:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2169f
	b 2170f
2169:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2170:
	cbnz x2, 2168b
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
2171:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2171b
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
2172:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2172b
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
2173:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2174:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2174b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2175:
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
2176:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2175b
2177:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2178:
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
	cbz x3, 2179f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2181:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2181b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2180f
2179:
2180:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2178b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2177b
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
2182:
	and x5, x2, x6
	cbz x5, 2183f
	b 2184f
2183:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2184:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2182b
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
2185:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2185b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2186:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2187f
	b 2188f
2187:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2188:
	cbnz x2, 2186b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2189:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2189b
	tst x15, x15
	movz x3, #0, lsl #0
	sub x4, x3, #1
	csel x3, x4, x3, eq
	ldr x0, [x0, #128]
	ldr x4, [x0, #360]
	and x3, x3, x4
	str x3, [x0, #360]
	ldr x8, [x0, #360]
	ldr x10, [x0, #320]
	ldr x11, [x0, #280]
	ldr x12, [x0, #288]
	ldr x13, [x0, #328]
	ldr x14, [x0, #336]
	add x2, x10, #0
	ldr x1, [x0, #256]
	add x9, x13, x13
	add x9, x9, x14
2190:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2190b
	add x2, x10, x13
	add x2, x2, x13
	add x2, x2, x14
	add x1, x11, #0
	add x9, x13, #0
2191:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2191b
	add x2, x10, x13
	add x2, x2, x13
	add x2, x2, x13
	add x2, x2, x14
	add x1, x12, #0
	add x9, x14, #0
2192:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2192b
	ldr x3, [x0, #360]
	movz x0, #1, lsl #0
	and x0, x3, x0
	b 217f
216:
	ldr x1, [x0, #320]
	ldr x2, [x0, #328]
	add x3, x2, x2
	add x2, x3, x2
	ldr x3, [x0, #336]
	add x2, x2, x3
	add x2, x2, x3
	movz x3, #0, lsl #0
2193:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2193b
	movz x0, #0, lsl #0
217:
	ret
	.p2align 6

vg_dsa_generate_parameters:
	sub sp, sp, #448
	str x19, [sp, #304]
	str x20, [sp, #312]
	str x21, [sp, #320]
	str x22, [sp, #328]
	str x23, [sp, #336]
	str x24, [sp, #344]
	str x25, [sp, #352]
	str x26, [sp, #360]
	str x27, [sp, #368]
	str x28, [sp, #376]
	umov x9, v8.d[0]
	str x9, [sp, #384]
	umov x9, v9.d[0]
	str x9, [sp, #392]
	umov x9, v10.d[0]
	str x9, [sp, #400]
	umov x9, v11.d[0]
	str x9, [sp, #408]
	umov x9, v12.d[0]
	str x9, [sp, #416]
	umov x9, v13.d[0]
	str x9, [sp, #424]
	umov x9, v14.d[0]
	str x9, [sp, #432]
	umov x9, v15.d[0]
	str x9, [sp, #440]
	str x30, [sp, #296]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x2, [sp, #136]
	str x3, [sp, #144]
	str x3, [sp, #208]
	str x4, [sp, #64]
	str x5, [sp, #72]
	str x6, [sp, #88]
	str x7, [sp, #104]
	ldr x3, [sp, #448]
	str x3, [sp, #112]
	ldr x3, [sp, #456]
	str x3, [sp, #120]
	ldr x3, [sp, #464]
	str x3, [sp, #40]
	ldr x3, [sp, #40]
	movz x4, #24576, lsl #0
	add x3, x3, x4
	str x3, [sp, #24]
	ldr x3, [sp, #40]
	movz x4, #24640, lsl #0
	add x3, x3, x4
	str x3, [sp, #32]
	ldr x3, [sp, #40]
	movz x4, #16384, lsl #0
	add x3, x3, x4
	str x3, [sp, #96]
	movz x3, #0, lsl #0
	str x3, [sp, #128]
	ldr x3, [sp, #136]
	sub x4, x3, #128
	cbz x4, 20f
	sub x4, x3, #256
	cbz x4, 22f
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
24:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 25f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 27f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 28f
27:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
28:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 29f
	b 210f
29:
211:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 211b
210:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 212f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 213f
212:
213:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 214f
	b 215f
214:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
216:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #352
	movz x9, #32, lsl #0
	cbnz x9, 217f
	b 218f
217:
219:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 219b
218:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #320
	movz x9, #32, lsl #0
	cbnz x9, 220f
	b 221f
220:
222:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 222b
221:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #288
	movz x9, #32, lsl #0
	cbnz x9, 223f
	b 224f
223:
225:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 225b
224:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #256
	movz x9, #32, lsl #0
	cbnz x9, 226f
	b 227f
226:
228:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 228b
227:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 229f
	b 230f
229:
231:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 231b
230:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 232f
	b 233f
232:
234:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 234b
233:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 235f
	b 236f
235:
237:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 237b
236:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 238f
	b 239f
238:
240:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 240b
239:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #8
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 241f
	b 242f
241:
243:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 243b
242:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #9
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 244f
	b 245f
244:
246:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 246b
245:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #10
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 247f
	b 248f
247:
249:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 249b
248:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #11
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 250f
	b 251f
250:
252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 252b
251:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 253f
	b 254f
253:
255:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 255b
254:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
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
	movz x3, #400, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #384, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
264:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	lsl x6, x12, #6
267:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
268:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
269:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
273:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
274:
	and x5, x2, x6
	cbz x5, 275f
	b 276f
275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 274b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
277:
	and x5, x2, x6
	cbz x5, 278f
	b 279f
278:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
279:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 277b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 280f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_3072}
	add w0, w0, #0
	cbz x0, 282f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 283f
282:
283:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 281f
280:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
281:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 284f
	b 285f
284:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #12
	str x4, [x0, #8]
	movz x4, #12288, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 286f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 287f
286:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
287:
285:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 216b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 288f
	b 289f
288:
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
289:
215:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 26f
25:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
26:
	cbz x0, 24b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
292:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 292b
	movz x0, #0, lsl #0
	b 291f
290:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 293f
	b 294f
293:
295:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 295b
294:
	movz x0, #1, lsl #0
291:
	b 23f
22:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
296:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 297f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 299f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 2100f
299:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
2100:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2101f
	b 2102f
2101:
2103:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2103b
2102:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 2104f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2105f
2104:
2105:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2106f
	b 2107f
2106:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2108:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 2109f
	b 2110f
2109:
2111:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2111b
2110:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 2112f
	b 2113f
2112:
2114:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2114b
2113:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 2115f
	b 2116f
2115:
2117:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2117b
2116:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 2118f
	b 2119f
2118:
2120:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2120b
2119:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 2121f
	b 2122f
2121:
2123:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2123b
2122:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 2124f
	b 2125f
2124:
2126:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2126b
2125:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 2127f
	b 2128f
2127:
2129:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2129b
2128:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 2130f
	b 2131f
2130:
2132:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2132b
2131:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2133f
	b 2134f
2133:
2135:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2135b
2134:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #32, lsl #0
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
	movz x3, #272, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #256, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2137:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2138f
	b 2139f
2138:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2139:
	cbnz x2, 2137b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2140:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2141:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2142f
	b 2143f
2142:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2143:
	cbnz x2, 2141b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2144:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2145:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
2147:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2148:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2149:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2151:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2147b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2152:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2153:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2154:
	and x5, x2, x6
	cbz x5, 2155f
	b 2156f
2155:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2156:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2154b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2157:
	and x5, x2, x6
	cbz x5, 2158f
	b 2159f
2158:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2159:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2157b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2160f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_2048}
	add w0, w0, #0
	cbz x0, 2162f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2163f
2162:
2163:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2161f
2160:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2161:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2164f
	b 2165f
2164:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #8
	str x4, [x0, #8]
	movz x4, #8192, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2166f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2167f
2166:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2167:
2165:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2108b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2168f
	b 2169f
2168:
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2169:
2107:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 298f
297:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
298:
	cbz x0, 296b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2170f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2172:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2172b
	movz x0, #0, lsl #0
	b 2171f
2170:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2173f
	b 2174f
2173:
2175:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2175b
2174:
	movz x0, #1, lsl #0
2171:
23:
	b 21f
20:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
2176:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #20, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 2177f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #20, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #20, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 2179f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 2180f
2179:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
2180:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2181f
	b 2182f
2181:
2183:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2183b
2182:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_160}
	add w0, w0, #0
	cbz x0, 2184f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2185f
2184:
2185:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2186f
	b 2187f
2186:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2188:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #120
	movz x9, #20, lsl #0
	cbnz x9, 2189f
	b 2190f
2189:
2191:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2191b
2190:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #100
	movz x9, #20, lsl #0
	cbnz x9, 2192f
	b 2193f
2192:
2194:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2194b
2193:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #80
	movz x9, #20, lsl #0
	cbnz x9, 2195f
	b 2196f
2195:
2197:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2197b
2196:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #60
	movz x9, #20, lsl #0
	cbnz x9, 2198f
	b 2199f
2198:
2200:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2200b
2199:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #40
	movz x9, #20, lsl #0
	cbnz x9, 2201f
	b 2202f
2201:
2203:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2203b
2202:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #20
	movz x9, #20, lsl #0
	cbnz x9, 2204f
	b 2205f
2204:
2206:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2206b
2205:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #20, lsl #0
	cbnz x9, 2207f
	b 2208f
2207:
2209:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2209b
2208:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2210f
	b 2211f
2210:
2212:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2212b
2211:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #16, lsl #0
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
	movz x3, #144, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #128, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #20, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2214:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2215f
	b 2216f
2215:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2216:
	cbnz x2, 2214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2218:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2219f
	b 2220f
2219:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2220:
	cbnz x2, 2218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2221:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	lsl x6, x12, #6
2224:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2225:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2226:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2230:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2231:
	and x5, x2, x6
	cbz x5, 2232f
	b 2233f
2232:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2233:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2234:
	and x5, x2, x6
	cbz x5, 2235f
	b 2236f
2235:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2236:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2234b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2237f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_1024}
	add w0, w0, #0
	cbz x0, 2239f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2240f
2239:
2240:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2238f
2237:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2238:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2241f
	b 2242f
2241:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #7
	str x4, [x0, #8]
	movz x4, #4096, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2243f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2244f
2243:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2244:
2242:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2188b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2245f
	b 2246f
2245:
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2246:
2187:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 2178f
2177:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
2178:
	cbz x0, 2176b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2247f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2249:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2249b
	movz x0, #0, lsl #0
	b 2248f
2247:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2250f
	b 2251f
2250:
2252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2252b
2251:
	movz x0, #1, lsl #0
2248:
21:
	ldr x9, [sp, #384]
	mov v8.d[0], x9
	ldr x9, [sp, #392]
	mov v9.d[0], x9
	ldr x9, [sp, #400]
	mov v10.d[0], x9
	ldr x9, [sp, #408]
	mov v11.d[0], x9
	ldr x9, [sp, #416]
	mov v12.d[0], x9
	ldr x9, [sp, #424]
	mov v13.d[0], x9
	ldr x9, [sp, #432]
	mov v14.d[0], x9
	ldr x9, [sp, #440]
	mov v15.d[0], x9
	ldr x19, [sp, #304]
	ldr x20, [sp, #312]
	ldr x21, [sp, #320]
	ldr x22, [sp, #328]
	ldr x23, [sp, #336]
	ldr x24, [sp, #344]
	ldr x25, [sp, #352]
	ldr x26, [sp, #360]
	ldr x27, [sp, #368]
	ldr x28, [sp, #376]
	ldr x30, [sp, #296]
	add sp, sp, #448
	ret
	.p2align 6

vg_dsa_generate_parameters_sha256_sha2:
	.arch_extension sha2
	sub sp, sp, #448
	str x19, [sp, #304]
	str x20, [sp, #312]
	str x21, [sp, #320]
	str x22, [sp, #328]
	str x23, [sp, #336]
	str x24, [sp, #344]
	str x25, [sp, #352]
	str x26, [sp, #360]
	str x27, [sp, #368]
	str x28, [sp, #376]
	umov x9, v8.d[0]
	str x9, [sp, #384]
	umov x9, v9.d[0]
	str x9, [sp, #392]
	umov x9, v10.d[0]
	str x9, [sp, #400]
	umov x9, v11.d[0]
	str x9, [sp, #408]
	umov x9, v12.d[0]
	str x9, [sp, #416]
	umov x9, v13.d[0]
	str x9, [sp, #424]
	umov x9, v14.d[0]
	str x9, [sp, #432]
	umov x9, v15.d[0]
	str x9, [sp, #440]
	str x30, [sp, #296]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x2, [sp, #136]
	str x3, [sp, #144]
	str x3, [sp, #208]
	str x4, [sp, #64]
	str x5, [sp, #72]
	str x6, [sp, #88]
	str x7, [sp, #104]
	ldr x3, [sp, #448]
	str x3, [sp, #112]
	ldr x3, [sp, #456]
	str x3, [sp, #120]
	ldr x3, [sp, #464]
	str x3, [sp, #40]
	ldr x3, [sp, #40]
	movz x4, #24576, lsl #0
	add x3, x3, x4
	str x3, [sp, #24]
	ldr x3, [sp, #40]
	movz x4, #24640, lsl #0
	add x3, x3, x4
	str x3, [sp, #32]
	ldr x3, [sp, #40]
	movz x4, #16384, lsl #0
	add x3, x3, x4
	str x3, [sp, #96]
	movz x3, #0, lsl #0
	str x3, [sp, #128]
	ldr x3, [sp, #136]
	sub x4, x3, #128
	cbz x4, 20f
	sub x4, x3, #256
	cbz x4, 22f
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
24:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 25f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 27f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 28f
27:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
28:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 29f
	b 210f
29:
211:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 211b
210:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 212f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 213f
212:
213:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 214f
	b 215f
214:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
216:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #352
	movz x9, #32, lsl #0
	cbnz x9, 217f
	b 218f
217:
219:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 219b
218:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #320
	movz x9, #32, lsl #0
	cbnz x9, 220f
	b 221f
220:
222:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 222b
221:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #288
	movz x9, #32, lsl #0
	cbnz x9, 223f
	b 224f
223:
225:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 225b
224:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #256
	movz x9, #32, lsl #0
	cbnz x9, 226f
	b 227f
226:
228:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 228b
227:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 229f
	b 230f
229:
231:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 231b
230:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 232f
	b 233f
232:
234:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 234b
233:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 235f
	b 236f
235:
237:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 237b
236:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 238f
	b 239f
238:
240:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 240b
239:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #8
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 241f
	b 242f
241:
243:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 243b
242:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #9
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 244f
	b 245f
244:
246:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 246b
245:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #10
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 247f
	b 248f
247:
249:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 249b
248:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #11
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 250f
	b 251f
250:
252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 252b
251:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 253f
	b 254f
253:
255:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 255b
254:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
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
	movz x3, #400, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #384, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
264:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	lsl x6, x12, #6
267:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
268:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
269:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
273:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
274:
	and x5, x2, x6
	cbz x5, 275f
	b 276f
275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 274b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
277:
	and x5, x2, x6
	cbz x5, 278f
	b 279f
278:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
279:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 277b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 280f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_3072}
	add w0, w0, #0
	cbz x0, 282f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 283f
282:
283:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 281f
280:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
281:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 284f
	b 285f
284:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #12
	str x4, [x0, #8]
	movz x4, #12288, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 286f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 287f
286:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
287:
285:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 216b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 288f
	b 289f
288:
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
289:
215:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 26f
25:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
26:
	cbz x0, 24b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
292:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 292b
	movz x0, #0, lsl #0
	b 291f
290:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 293f
	b 294f
293:
295:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 295b
294:
	movz x0, #1, lsl #0
291:
	b 23f
22:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
296:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 297f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 299f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 2100f
299:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
2100:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2101f
	b 2102f
2101:
2103:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2103b
2102:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 2104f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2105f
2104:
2105:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2106f
	b 2107f
2106:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2108:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 2109f
	b 2110f
2109:
2111:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2111b
2110:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 2112f
	b 2113f
2112:
2114:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2114b
2113:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 2115f
	b 2116f
2115:
2117:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2117b
2116:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 2118f
	b 2119f
2118:
2120:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2120b
2119:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 2121f
	b 2122f
2121:
2123:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2123b
2122:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 2124f
	b 2125f
2124:
2126:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2126b
2125:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 2127f
	b 2128f
2127:
2129:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2129b
2128:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 2130f
	b 2131f
2130:
2132:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2132b
2131:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2133f
	b 2134f
2133:
2135:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2135b
2134:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #32, lsl #0
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
	movz x3, #272, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #256, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2137:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2138f
	b 2139f
2138:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2139:
	cbnz x2, 2137b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2140:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2141:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2142f
	b 2143f
2142:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2143:
	cbnz x2, 2141b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2144:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2145:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
2147:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2148:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2149:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2151:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2147b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2152:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2153:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2154:
	and x5, x2, x6
	cbz x5, 2155f
	b 2156f
2155:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2156:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2154b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2157:
	and x5, x2, x6
	cbz x5, 2158f
	b 2159f
2158:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2159:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2157b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2160f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_2048}
	add w0, w0, #0
	cbz x0, 2162f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2163f
2162:
2163:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2161f
2160:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2161:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2164f
	b 2165f
2164:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #8
	str x4, [x0, #8]
	movz x4, #8192, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2166f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2167f
2166:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2167:
2165:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2108b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2168f
	b 2169f
2168:
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2169:
2107:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 298f
297:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
298:
	cbz x0, 296b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2170f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2172:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2172b
	movz x0, #0, lsl #0
	b 2171f
2170:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2173f
	b 2174f
2173:
2175:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2175b
2174:
	movz x0, #1, lsl #0
2171:
23:
	b 21f
20:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
2176:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #20, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 2177f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #20, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #20, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 2179f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 2180f
2179:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
2180:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2181f
	b 2182f
2181:
2183:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2183b
2182:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_160}
	add w0, w0, #0
	cbz x0, 2184f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2185f
2184:
2185:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2186f
	b 2187f
2186:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2188:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #120
	movz x9, #20, lsl #0
	cbnz x9, 2189f
	b 2190f
2189:
2191:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2191b
2190:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #100
	movz x9, #20, lsl #0
	cbnz x9, 2192f
	b 2193f
2192:
2194:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2194b
2193:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #80
	movz x9, #20, lsl #0
	cbnz x9, 2195f
	b 2196f
2195:
2197:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2197b
2196:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #60
	movz x9, #20, lsl #0
	cbnz x9, 2198f
	b 2199f
2198:
2200:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2200b
2199:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #40
	movz x9, #20, lsl #0
	cbnz x9, 2201f
	b 2202f
2201:
2203:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2203b
2202:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #20
	movz x9, #20, lsl #0
	cbnz x9, 2204f
	b 2205f
2204:
2206:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2206b
2205:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #20, lsl #0
	cbnz x9, 2207f
	b 2208f
2207:
2209:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2209b
2208:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2210f
	b 2211f
2210:
2212:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2212b
2211:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #16, lsl #0
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
	movz x3, #144, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #128, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #20, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2214:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2215f
	b 2216f
2215:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2216:
	cbnz x2, 2214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2218:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2219f
	b 2220f
2219:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2220:
	cbnz x2, 2218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2221:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	lsl x6, x12, #6
2224:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2225:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2226:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2230:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2231:
	and x5, x2, x6
	cbz x5, 2232f
	b 2233f
2232:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2233:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2234:
	and x5, x2, x6
	cbz x5, 2235f
	b 2236f
2235:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2236:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2234b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2237f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_1024}
	add w0, w0, #0
	cbz x0, 2239f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2240f
2239:
2240:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2238f
2237:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2238:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2241f
	b 2242f
2241:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #7
	str x4, [x0, #8]
	movz x4, #4096, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2243f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2244f
2243:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2244:
2242:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2188b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2245f
	b 2246f
2245:
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2246:
2187:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 2178f
2177:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
2178:
	cbz x0, 2176b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2247f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2249:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2249b
	movz x0, #0, lsl #0
	b 2248f
2247:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2250f
	b 2251f
2250:
2252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2252b
2251:
	movz x0, #1, lsl #0
2248:
21:
	ldr x9, [sp, #384]
	mov v8.d[0], x9
	ldr x9, [sp, #392]
	mov v9.d[0], x9
	ldr x9, [sp, #400]
	mov v10.d[0], x9
	ldr x9, [sp, #408]
	mov v11.d[0], x9
	ldr x9, [sp, #416]
	mov v12.d[0], x9
	ldr x9, [sp, #424]
	mov v13.d[0], x9
	ldr x9, [sp, #432]
	mov v14.d[0], x9
	ldr x9, [sp, #440]
	mov v15.d[0], x9
	ldr x19, [sp, #304]
	ldr x20, [sp, #312]
	ldr x21, [sp, #320]
	ldr x22, [sp, #328]
	ldr x23, [sp, #336]
	ldr x24, [sp, #344]
	ldr x25, [sp, #352]
	ldr x26, [sp, #360]
	ldr x27, [sp, #368]
	ldr x28, [sp, #376]
	ldr x30, [sp, #296]
	add sp, sp, #448
	ret
	.arch_extension nosha2
	.p2align 6

vg_dsa_generate_parameters_sha1_sha2:
	.arch_extension sha2
	sub sp, sp, #448
	str x19, [sp, #304]
	str x20, [sp, #312]
	str x21, [sp, #320]
	str x22, [sp, #328]
	str x23, [sp, #336]
	str x24, [sp, #344]
	str x25, [sp, #352]
	str x26, [sp, #360]
	str x27, [sp, #368]
	str x28, [sp, #376]
	umov x9, v8.d[0]
	str x9, [sp, #384]
	umov x9, v9.d[0]
	str x9, [sp, #392]
	umov x9, v10.d[0]
	str x9, [sp, #400]
	umov x9, v11.d[0]
	str x9, [sp, #408]
	umov x9, v12.d[0]
	str x9, [sp, #416]
	umov x9, v13.d[0]
	str x9, [sp, #424]
	umov x9, v14.d[0]
	str x9, [sp, #432]
	umov x9, v15.d[0]
	str x9, [sp, #440]
	str x30, [sp, #296]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x2, [sp, #136]
	str x3, [sp, #144]
	str x3, [sp, #208]
	str x4, [sp, #64]
	str x5, [sp, #72]
	str x6, [sp, #88]
	str x7, [sp, #104]
	ldr x3, [sp, #448]
	str x3, [sp, #112]
	ldr x3, [sp, #456]
	str x3, [sp, #120]
	ldr x3, [sp, #464]
	str x3, [sp, #40]
	ldr x3, [sp, #40]
	movz x4, #24576, lsl #0
	add x3, x3, x4
	str x3, [sp, #24]
	ldr x3, [sp, #40]
	movz x4, #24640, lsl #0
	add x3, x3, x4
	str x3, [sp, #32]
	ldr x3, [sp, #40]
	movz x4, #16384, lsl #0
	add x3, x3, x4
	str x3, [sp, #96]
	movz x3, #0, lsl #0
	str x3, [sp, #128]
	ldr x3, [sp, #136]
	sub x4, x3, #128
	cbz x4, 20f
	sub x4, x3, #256
	cbz x4, 22f
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
24:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 25f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 27f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 28f
27:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
28:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 29f
	b 210f
29:
211:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 211b
210:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 212f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 213f
212:
213:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 214f
	b 215f
214:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
216:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #352
	movz x9, #32, lsl #0
	cbnz x9, 217f
	b 218f
217:
219:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 219b
218:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #320
	movz x9, #32, lsl #0
	cbnz x9, 220f
	b 221f
220:
222:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 222b
221:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #288
	movz x9, #32, lsl #0
	cbnz x9, 223f
	b 224f
223:
225:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 225b
224:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #256
	movz x9, #32, lsl #0
	cbnz x9, 226f
	b 227f
226:
228:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 228b
227:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 229f
	b 230f
229:
231:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 231b
230:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 232f
	b 233f
232:
234:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 234b
233:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 235f
	b 236f
235:
237:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 237b
236:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 238f
	b 239f
238:
240:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 240b
239:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #8
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 241f
	b 242f
241:
243:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 243b
242:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #9
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 244f
	b 245f
244:
246:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 246b
245:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #10
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 247f
	b 248f
247:
249:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 249b
248:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #11
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 250f
	b 251f
250:
252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 252b
251:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 253f
	b 254f
253:
255:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 255b
254:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
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
	movz x3, #400, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #384, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
264:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	lsl x6, x12, #6
267:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
268:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
269:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
273:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
274:
	and x5, x2, x6
	cbz x5, 275f
	b 276f
275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 274b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
277:
	and x5, x2, x6
	cbz x5, 278f
	b 279f
278:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
279:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 277b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 280f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_3072}
	add w0, w0, #0
	cbz x0, 282f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 283f
282:
283:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 281f
280:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
281:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 284f
	b 285f
284:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #12
	str x4, [x0, #8]
	movz x4, #12288, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 286f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 287f
286:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
287:
285:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 216b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 288f
	b 289f
288:
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
289:
215:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 26f
25:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
26:
	cbz x0, 24b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
292:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 292b
	movz x0, #0, lsl #0
	b 291f
290:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 293f
	b 294f
293:
295:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 295b
294:
	movz x0, #1, lsl #0
291:
	b 23f
22:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
296:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 297f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 299f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 2100f
299:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
2100:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2101f
	b 2102f
2101:
2103:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2103b
2102:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 2104f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2105f
2104:
2105:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2106f
	b 2107f
2106:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2108:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 2109f
	b 2110f
2109:
2111:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2111b
2110:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 2112f
	b 2113f
2112:
2114:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2114b
2113:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 2115f
	b 2116f
2115:
2117:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2117b
2116:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 2118f
	b 2119f
2118:
2120:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2120b
2119:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 2121f
	b 2122f
2121:
2123:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2123b
2122:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 2124f
	b 2125f
2124:
2126:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2126b
2125:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 2127f
	b 2128f
2127:
2129:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2129b
2128:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 2130f
	b 2131f
2130:
2132:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2132b
2131:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2133f
	b 2134f
2133:
2135:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2135b
2134:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #32, lsl #0
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
	movz x3, #272, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #256, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2137:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2138f
	b 2139f
2138:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2139:
	cbnz x2, 2137b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2140:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2141:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2142f
	b 2143f
2142:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2143:
	cbnz x2, 2141b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2144:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2145:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
2147:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2148:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2149:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2151:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2147b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2152:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2153:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2154:
	and x5, x2, x6
	cbz x5, 2155f
	b 2156f
2155:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2156:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2154b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2157:
	and x5, x2, x6
	cbz x5, 2158f
	b 2159f
2158:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2159:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2157b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2160f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_2048}
	add w0, w0, #0
	cbz x0, 2162f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2163f
2162:
2163:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2161f
2160:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2161:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2164f
	b 2165f
2164:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #8
	str x4, [x0, #8]
	movz x4, #8192, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2166f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2167f
2166:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2167:
2165:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2108b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2168f
	b 2169f
2168:
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2169:
2107:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 298f
297:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
298:
	cbz x0, 296b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2170f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2172:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2172b
	movz x0, #0, lsl #0
	b 2171f
2170:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2173f
	b 2174f
2173:
2175:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2175b
2174:
	movz x0, #1, lsl #0
2171:
23:
	b 21f
20:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
2176:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #20, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 2177f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #20, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #20, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 2179f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	b 2180f
2179:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
2180:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2181f
	b 2182f
2181:
2183:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2183b
2182:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_160}
	add w0, w0, #0
	cbz x0, 2184f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2185f
2184:
2185:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2186f
	b 2187f
2186:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2188:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #120
	movz x9, #20, lsl #0
	cbnz x9, 2189f
	b 2190f
2189:
2191:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2191b
2190:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #100
	movz x9, #20, lsl #0
	cbnz x9, 2192f
	b 2193f
2192:
2194:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2194b
2193:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #80
	movz x9, #20, lsl #0
	cbnz x9, 2195f
	b 2196f
2195:
2197:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2197b
2196:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #60
	movz x9, #20, lsl #0
	cbnz x9, 2198f
	b 2199f
2198:
2200:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2200b
2199:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #40
	movz x9, #20, lsl #0
	cbnz x9, 2201f
	b 2202f
2201:
2203:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2203b
2202:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #20
	movz x9, #20, lsl #0
	cbnz x9, 2204f
	b 2205f
2204:
2206:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2206b
2205:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #20, lsl #0
	cbnz x9, 2207f
	b 2208f
2207:
2209:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2209b
2208:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2210f
	b 2211f
2210:
2212:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2212b
2211:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #16, lsl #0
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
	movz x3, #144, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #128, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #20, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2214:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2215f
	b 2216f
2215:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2216:
	cbnz x2, 2214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2218:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2219f
	b 2220f
2219:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2220:
	cbnz x2, 2218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2221:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	lsl x6, x12, #6
2224:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2225:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2226:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2230:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2231:
	and x5, x2, x6
	cbz x5, 2232f
	b 2233f
2232:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2233:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2234:
	and x5, x2, x6
	cbz x5, 2235f
	b 2236f
2235:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2236:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2234b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2237f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_1024}
	add w0, w0, #0
	cbz x0, 2239f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2240f
2239:
2240:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2238f
2237:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2238:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2241f
	b 2242f
2241:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #7
	str x4, [x0, #8]
	movz x4, #4096, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2243f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2244f
2243:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2244:
2242:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2188b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2245f
	b 2246f
2245:
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2246:
2187:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 2178f
2177:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
2178:
	cbz x0, 2176b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2247f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2249:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2249b
	movz x0, #0, lsl #0
	b 2248f
2247:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2250f
	b 2251f
2250:
2252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2252b
2251:
	movz x0, #1, lsl #0
2248:
21:
	ldr x9, [sp, #384]
	mov v8.d[0], x9
	ldr x9, [sp, #392]
	mov v9.d[0], x9
	ldr x9, [sp, #400]
	mov v10.d[0], x9
	ldr x9, [sp, #408]
	mov v11.d[0], x9
	ldr x9, [sp, #416]
	mov v12.d[0], x9
	ldr x9, [sp, #424]
	mov v13.d[0], x9
	ldr x9, [sp, #432]
	mov v14.d[0], x9
	ldr x9, [sp, #440]
	mov v15.d[0], x9
	ldr x19, [sp, #304]
	ldr x20, [sp, #312]
	ldr x21, [sp, #320]
	ldr x22, [sp, #328]
	ldr x23, [sp, #336]
	ldr x24, [sp, #344]
	ldr x25, [sp, #352]
	ldr x26, [sp, #360]
	ldr x27, [sp, #368]
	ldr x28, [sp, #376]
	ldr x30, [sp, #296]
	add sp, sp, #448
	ret
	.arch_extension nosha2
	.p2align 6

vg_dsa_generate_parameters_sha1_sha2_sha256_sha2:
	.arch_extension sha2
	sub sp, sp, #448
	str x19, [sp, #304]
	str x20, [sp, #312]
	str x21, [sp, #320]
	str x22, [sp, #328]
	str x23, [sp, #336]
	str x24, [sp, #344]
	str x25, [sp, #352]
	str x26, [sp, #360]
	str x27, [sp, #368]
	str x28, [sp, #376]
	umov x9, v8.d[0]
	str x9, [sp, #384]
	umov x9, v9.d[0]
	str x9, [sp, #392]
	umov x9, v10.d[0]
	str x9, [sp, #400]
	umov x9, v11.d[0]
	str x9, [sp, #408]
	umov x9, v12.d[0]
	str x9, [sp, #416]
	umov x9, v13.d[0]
	str x9, [sp, #424]
	umov x9, v14.d[0]
	str x9, [sp, #432]
	umov x9, v15.d[0]
	str x9, [sp, #440]
	str x30, [sp, #296]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x2, [sp, #136]
	str x3, [sp, #144]
	str x3, [sp, #208]
	str x4, [sp, #64]
	str x5, [sp, #72]
	str x6, [sp, #88]
	str x7, [sp, #104]
	ldr x3, [sp, #448]
	str x3, [sp, #112]
	ldr x3, [sp, #456]
	str x3, [sp, #120]
	ldr x3, [sp, #464]
	str x3, [sp, #40]
	ldr x3, [sp, #40]
	movz x4, #24576, lsl #0
	add x3, x3, x4
	str x3, [sp, #24]
	ldr x3, [sp, #40]
	movz x4, #24640, lsl #0
	add x3, x3, x4
	str x3, [sp, #32]
	ldr x3, [sp, #40]
	movz x4, #16384, lsl #0
	add x3, x3, x4
	str x3, [sp, #96]
	movz x3, #0, lsl #0
	str x3, [sp, #128]
	ldr x3, [sp, #136]
	sub x4, x3, #128
	cbz x4, 20f
	sub x4, x3, #256
	cbz x4, 22f
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
24:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 25f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 27f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 28f
27:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
28:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 29f
	b 210f
29:
211:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 211b
210:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 212f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 213f
212:
213:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 214f
	b 215f
214:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
216:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #352
	movz x9, #32, lsl #0
	cbnz x9, 217f
	b 218f
217:
219:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 219b
218:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #320
	movz x9, #32, lsl #0
	cbnz x9, 220f
	b 221f
220:
222:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 222b
221:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #288
	movz x9, #32, lsl #0
	cbnz x9, 223f
	b 224f
223:
225:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 225b
224:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #256
	movz x9, #32, lsl #0
	cbnz x9, 226f
	b 227f
226:
228:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 228b
227:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 229f
	b 230f
229:
231:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 231b
230:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 232f
	b 233f
232:
234:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 234b
233:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 235f
	b 236f
235:
237:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 237b
236:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 238f
	b 239f
238:
240:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 240b
239:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #8
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 241f
	b 242f
241:
243:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 243b
242:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #9
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 244f
	b 245f
244:
246:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 246b
245:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #10
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 247f
	b 248f
247:
249:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 249b
248:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #11
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 250f
	b 251f
250:
252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 252b
251:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 253f
	b 254f
253:
255:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 255b
254:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
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
	movz x3, #400, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #384, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
264:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 264b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
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
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	lsl x6, x12, #6
267:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
268:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 268b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
269:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
271:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
273:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
274:
	and x5, x2, x6
	cbz x5, 275f
	b 276f
275:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
276:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 274b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
277:
	and x5, x2, x6
	cbz x5, 278f
	b 279f
278:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
279:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 277b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 280f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_3072}
	add w0, w0, #0
	cbz x0, 282f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 283f
282:
283:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 281f
280:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
281:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 284f
	b 285f
284:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #12
	str x4, [x0, #8]
	movz x4, #12288, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 286f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 287f
286:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
287:
285:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 216b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 288f
	b 289f
288:
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
289:
215:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 26f
25:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
26:
	cbz x0, 24b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
292:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 292b
	movz x0, #0, lsl #0
	b 291f
290:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 293f
	b 294f
293:
295:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 295b
294:
	movz x0, #1, lsl #0
291:
	b 23f
22:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
296:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #32, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 297f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #32, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #32, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 299f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 2100f
299:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
2100:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2101f
	b 2102f
2101:
2103:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2103b
2102:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_256}
	add w0, w0, #0
	cbz x0, 2104f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2105f
2104:
2105:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2106f
	b 2107f
2106:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2108:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #224
	movz x9, #32, lsl #0
	cbnz x9, 2109f
	b 2110f
2109:
2111:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2111b
2110:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #192
	movz x9, #32, lsl #0
	cbnz x9, 2112f
	b 2113f
2112:
2114:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2114b
2113:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #160
	movz x9, #32, lsl #0
	cbnz x9, 2115f
	b 2116f
2115:
2117:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2117b
2116:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #128
	movz x9, #32, lsl #0
	cbnz x9, 2118f
	b 2119f
2118:
2120:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2120b
2119:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #96
	movz x9, #32, lsl #0
	cbnz x9, 2121f
	b 2122f
2121:
2123:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2123b
2122:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #64
	movz x9, #32, lsl #0
	cbnz x9, 2124f
	b 2125f
2124:
2126:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2126b
2125:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #32
	movz x9, #32, lsl #0
	cbnz x9, 2127f
	b 2128f
2127:
2129:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2129b
2128:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #7
	ldrb w3, [x1, #31]
	add x0, x0, x3
	strb w0, [x2, #31]
	lsr x0, x0, #8
	ldrb w3, [x1, #30]
	add x0, x0, x3
	strb w0, [x2, #30]
	lsr x0, x0, #8
	ldrb w3, [x1, #29]
	add x0, x0, x3
	strb w0, [x2, #29]
	lsr x0, x0, #8
	ldrb w3, [x1, #28]
	add x0, x0, x3
	strb w0, [x2, #28]
	lsr x0, x0, #8
	ldrb w3, [x1, #27]
	add x0, x0, x3
	strb w0, [x2, #27]
	lsr x0, x0, #8
	ldrb w3, [x1, #26]
	add x0, x0, x3
	strb w0, [x2, #26]
	lsr x0, x0, #8
	ldrb w3, [x1, #25]
	add x0, x0, x3
	strb w0, [x2, #25]
	lsr x0, x0, #8
	ldrb w3, [x1, #24]
	add x0, x0, x3
	strb w0, [x2, #24]
	lsr x0, x0, #8
	ldrb w3, [x1, #23]
	add x0, x0, x3
	strb w0, [x2, #23]
	lsr x0, x0, #8
	ldrb w3, [x1, #22]
	add x0, x0, x3
	strb w0, [x2, #22]
	lsr x0, x0, #8
	ldrb w3, [x1, #21]
	add x0, x0, x3
	strb w0, [x2, #21]
	lsr x0, x0, #8
	ldrb w3, [x1, #20]
	add x0, x0, x3
	strb w0, [x2, #20]
	lsr x0, x0, #8
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #32, lsl #0
	cbnz x9, 2130f
	b 2131f
2130:
2132:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2132b
2131:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2133f
	b 2134f
2133:
2135:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2135b
2134:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #32, lsl #0
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
	movz x3, #272, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #256, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #32, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2137:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2138f
	b 2139f
2138:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2139:
	cbnz x2, 2137b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2140:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2141:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2142f
	b 2143f
2142:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2143:
	cbnz x2, 2141b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2144:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2145:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
2147:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2148:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2149:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
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
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2151:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2147b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2152:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2152b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2153:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2154:
	and x5, x2, x6
	cbz x5, 2155f
	b 2156f
2155:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2156:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2154b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2157:
	and x5, x2, x6
	cbz x5, 2158f
	b 2159f
2158:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2159:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2157b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2160f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_2048}
	add w0, w0, #0
	cbz x0, 2162f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2163f
2162:
2163:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2161f
2160:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2161:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2164f
	b 2165f
2164:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #8
	str x4, [x0, #8]
	movz x4, #8192, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2166f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2167f
2166:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2167:
2165:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2108b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2168f
	b 2169f
2168:
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2169:
2107:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 298f
297:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
298:
	cbz x0, 296b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2170f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2172:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2172b
	movz x0, #0, lsl #0
	b 2171f
2170:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2173f
	b 2174f
2173:
2175:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2175b
2174:
	movz x0, #1, lsl #0
2171:
23:
	b 21f
20:
	movz x0, #0, lsl #0
	add x15, sp, #80
	str x0, [x15, #0]
2176:
	ldr x3, [sp, #72]
	ldr x4, [sp, #80]
	sub x3, x3, x4
	movz x5, #20, lsl #0
	subs x3, x3, x5
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x0, x5, x4, hs
	cbnz x0, 2177f
	ldr x3, [sp, #64]
	ldr x4, [sp, #80]
	add x3, x3, x4
	movz x5, #20, lsl #0
	add x4, x4, x5
	add x15, sp, #8
	str x3, [x15, #0]
	add x15, sp, #80
	str x4, [x15, #0]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [sp, #0]
	ldr x3, [sp, #8]
	str x3, [sp, #200]
	movz x3, #20, lsl #0
	str x3, [sp, #208]
	ldr x0, [sp, #208]
	sub x0, x0, #20
	cbz x0, 2179f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha256_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	b 2180f
2179:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
2180:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2181f
	b 2182f
2181:
2183:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2183b
2182:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_160}
	add w0, w0, #0
	cbz x0, 2184f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2185f
2184:
2185:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2186f
	b 2187f
2186:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2188:
	ldr x3, [x0, #8]
	ldr x4, [sp, #40]
	movz x5, #25024, lsl #0
	add x4, x4, x5
	str x4, [sp, #0]
	str x3, [sp, #16]
	ldr x4, [sp, #24]
	str x4, [sp, #200]
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #0
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #120
	movz x9, #20, lsl #0
	cbnz x9, 2189f
	b 2190f
2189:
2191:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2191b
2190:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #1
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #100
	movz x9, #20, lsl #0
	cbnz x9, 2192f
	b 2193f
2192:
2194:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2194b
2193:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #2
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #80
	movz x9, #20, lsl #0
	cbnz x9, 2195f
	b 2196f
2195:
2197:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2197b
2196:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #3
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #60
	movz x9, #20, lsl #0
	cbnz x9, 2198f
	b 2199f
2198:
2200:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2200b
2199:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #4
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #40
	movz x9, #20, lsl #0
	cbnz x9, 2201f
	b 2202f
2201:
2203:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2203b
2202:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #5
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #20
	movz x9, #20, lsl #0
	cbnz x9, 2204f
	b 2205f
2204:
2206:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2206b
2205:
	ldr x1, [sp, #8]
	ldr x2, [sp, #24]
	ldr x0, [sp, #16]
	add x0, x0, #6
	ldrb w3, [x1, #19]
	add x0, x0, x3
	strb w0, [x2, #19]
	lsr x0, x0, #8
	ldrb w3, [x1, #18]
	add x0, x0, x3
	strb w0, [x2, #18]
	lsr x0, x0, #8
	ldrb w3, [x1, #17]
	add x0, x0, x3
	strb w0, [x2, #17]
	lsr x0, x0, #8
	ldrb w3, [x1, #16]
	add x0, x0, x3
	strb w0, [x2, #16]
	lsr x0, x0, #8
	ldrb w3, [x1, #15]
	add x0, x0, x3
	strb w0, [x2, #15]
	lsr x0, x0, #8
	ldrb w3, [x1, #14]
	add x0, x0, x3
	strb w0, [x2, #14]
	lsr x0, x0, #8
	ldrb w3, [x1, #13]
	add x0, x0, x3
	strb w0, [x2, #13]
	lsr x0, x0, #8
	ldrb w3, [x1, #12]
	add x0, x0, x3
	strb w0, [x2, #12]
	lsr x0, x0, #8
	ldrb w3, [x1, #11]
	add x0, x0, x3
	strb w0, [x2, #11]
	lsr x0, x0, #8
	ldrb w3, [x1, #10]
	add x0, x0, x3
	strb w0, [x2, #10]
	lsr x0, x0, #8
	ldrb w3, [x1, #9]
	add x0, x0, x3
	strb w0, [x2, #9]
	lsr x0, x0, #8
	ldrb w3, [x1, #8]
	add x0, x0, x3
	strb w0, [x2, #8]
	lsr x0, x0, #8
	ldrb w3, [x1, #7]
	add x0, x0, x3
	strb w0, [x2, #7]
	lsr x0, x0, #8
	ldrb w3, [x1, #6]
	add x0, x0, x3
	strb w0, [x2, #6]
	lsr x0, x0, #8
	ldrb w3, [x1, #5]
	add x0, x0, x3
	strb w0, [x2, #5]
	lsr x0, x0, #8
	ldrb w3, [x1, #4]
	add x0, x0, x3
	strb w0, [x2, #4]
	lsr x0, x0, #8
	ldrb w3, [x1, #3]
	add x0, x0, x3
	strb w0, [x2, #3]
	lsr x0, x0, #8
	ldrb w3, [x1, #2]
	add x0, x0, x3
	strb w0, [x2, #2]
	lsr x0, x0, #8
	ldrb w3, [x1, #1]
	add x0, x0, x3
	strb w0, [x2, #1]
	lsr x0, x0, #8
	ldrb w3, [x1, #0]
	add x0, x0, x3
	strb w0, [x2, #0]
	lsr x0, x0, #8
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x2, [sp, #32]
	add x2, x2, #0
	movz x9, #20, lsl #0
	cbnz x9, 2207f
	b 2208f
2207:
2209:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2209b
2208:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2210f
	b 2211f
2210:
2212:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2212b
2211:
	ldrb w0, [x13, #0]
	movz x4, #128, lsl #0
	orr x0, x0, x4
	strb w0, [x13, #0]
	add x2, x13, x14
	sub x2, x2, #1
	ldrb w0, [x2, #0]
	movz x4, #1, lsl #0
	orr x0, x0, x4
	strb w0, [x2, #0]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #16, lsl #0
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
	movz x3, #144, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #25024, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #128, lsl #0
	str x3, [x0, #136]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #144]
	movz x3, #20, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25472, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #40]
	movz x4, #25856, lsl #0
	add x3, x3, x4
	str x3, [x0, #168]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	str x3, [x0, #176]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
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
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2214:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2215f
	b 2216f
2215:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2216:
	cbnz x2, 2214b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2218:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2219f
	b 2220f
2219:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2220:
	cbnz x2, 2218b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2221:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2223:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2223b
	lsl x6, x12, #6
2224:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2225:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2225b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2226:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2226b
	movz x7, #0, lsl #0
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
2227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x13, #0]
	sub x4, x7, #1
	csel x15, x4, x7, hs
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #1
	movz x3, #1, lsl #0
	subs x3, x15, x3
2228:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2224b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
2229:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x16, #0]
	add x3, x3, #1
	str x3, [x16, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2230:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2230b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #160]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2231:
	and x5, x2, x6
	cbz x5, 2232f
	b 2233f
2232:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2233:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2231b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2234:
	and x5, x2, x6
	cbz x5, 2235f
	b 2236f
2235:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2236:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2234b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2237f
	ldr x0, [sp, #40]
	movz x1, #5120, lsl #0
	ldr x2, [sp, #112]
	ldr x5, [sp, #128]
	add x2, x2, x5
	ldr x3, [sp, #120]
	sub x3, x3, x5
	add x4, sp, #152
	bl {vg_dsa_probable_prime_1024}
	add w0, w0, #0
	cbz x0, 2239f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2240f
2239:
2240:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2238f
2237:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2238:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2241f
	b 2242f
2241:
	ldr x3, [x0, #0]
	add x3, x3, #1
	str x3, [x0, #0]
	ldr x4, [x0, #8]
	add x4, x4, #7
	str x4, [x0, #8]
	movz x4, #4096, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2243f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2244f
2243:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2244:
2242:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2188b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2245f
	b 2246f
2245:
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	add w0, w0, #0
	movz x3, #3, lsl #0
	sub x3, x3, x0
	sub x3, x3, x0
	str x3, [sp, #152]
2246:
2187:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	b 2178f
2177:
	movz x0, #3, lsl #0
	add x15, sp, #152
	str x0, [x15, #0]
	movz x0, #1, lsl #0
2178:
	cbz x0, 2176b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2247f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2249:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2249b
	movz x0, #0, lsl #0
	b 2248f
2247:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2250f
	b 2251f
2250:
2252:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2252b
2251:
	movz x0, #1, lsl #0
2248:
21:
	ldr x9, [sp, #384]
	mov v8.d[0], x9
	ldr x9, [sp, #392]
	mov v9.d[0], x9
	ldr x9, [sp, #400]
	mov v10.d[0], x9
	ldr x9, [sp, #408]
	mov v11.d[0], x9
	ldr x9, [sp, #416]
	mov v12.d[0], x9
	ldr x9, [sp, #424]
	mov v13.d[0], x9
	ldr x9, [sp, #432]
	mov v14.d[0], x9
	ldr x9, [sp, #440]
	mov v15.d[0], x9
	ldr x19, [sp, #304]
	ldr x20, [sp, #312]
	ldr x21, [sp, #320]
	ldr x22, [sp, #328]
	ldr x23, [sp, #336]
	ldr x24, [sp, #344]
	ldr x25, [sp, #352]
	ldr x26, [sp, #360]
	ldr x27, [sp, #368]
	ldr x28, [sp, #376]
	ldr x30, [sp, #296]
	add sp, sp, #448
	ret
	.arch_extension nosha2
	.p2align 6
