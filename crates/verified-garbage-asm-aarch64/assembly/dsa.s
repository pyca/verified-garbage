// The functions of `src/dsa.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_parameter_search_init:
	sub x9, x1, #128
	cbz x9, 20f
	sub x9, x1, #256
	cbz x9, 22f
	sub x9, x1, #384
	cbz x9, 24f
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	movz x0, #0, lsl #0
	b 25f
24:
	movz x9, #4096, lsl #0
	str x9, [x0, #0]
	str x1, [x0, #8]
	lsl x10, x1, #15
	add x10, x10, x1
	str x10, [x0, #16]
	lsl x10, x1, #9
	str x10, [x0, #24]
	movz x0, #1, lsl #0
25:
	b 23f
22:
	movz x9, #4096, lsl #0
	str x9, [x0, #0]
	str x1, [x0, #8]
	lsl x10, x1, #15
	add x10, x10, x1
	str x10, [x0, #16]
	lsl x10, x1, #9
	str x10, [x0, #24]
	movz x0, #1, lsl #0
23:
	b 21f
20:
	movz x9, #4096, lsl #0
	str x9, [x0, #0]
	str x1, [x0, #8]
	lsl x10, x1, #15
	add x10, x10, x1
	str x10, [x0, #16]
	lsl x10, x1, #9
	str x10, [x0, #24]
	movz x0, #1, lsl #0
21:
	ret
	.p2align 6

vg_dsa_sign_random_prevalidated:
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
	bl {vg_dsa_sign_prevalidated}
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

vg_dsa_validate_private_key:
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
	ldr x3, [x11, #288]
	str x3, [x11, #304]
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
2138:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2142:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2143:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2143b
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
	ldr x3, [x0, #304]
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
2144:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2145:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2146f
	b 2147f
2146:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2147:
	cbnz x2, 2145b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2148:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2148b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2149:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2149b
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
2150:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2151f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2153f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2155:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2155b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2156:
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
	cbnz x13, 2156b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2157:
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
2158:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2158b
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
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
2160:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2161:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2161b
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
2162:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2163:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2157b
	b 2154f
2153:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2164f
2166:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2166b
	b 2165f
2164:
2165:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2167:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2167b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2168:
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
2169:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2169b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2170:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2170b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2171:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2171b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2168b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2172:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2172b
2154:
	b 2152f
2151:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2173:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2174:
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
2175:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2174b
2152:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2178:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2178b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2179:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2180f
	b 2181f
2180:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2181:
	cbnz x2, 2179b
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
2182:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2182b
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
2183:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2183b
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
2184:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2184b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2185:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2185b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2186:
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
2187:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2187b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2186b
2188:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2189:
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
2190:
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
2191:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2191b
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
	cbnz x4, 2190b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2189b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2188b
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
2192:
	and x5, x2, x6
	cbz x5, 2193f
	b 2194f
2193:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2194:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2192b
	ldr x0, [x0, #128]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x3, [x0, #280]
	add x2, x3, #0
	ldr x9, [x0, #328]
	movz x8, #0, lsl #0
2195:
	ldrb w3, [x1, #0]
	ldrb w10, [x2, #0]
	eor x3, x3, x10
	orr x8, x8, x3
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2195b
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
	bl {vg_dsa_derive_key_checked}
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

vg_dsa_parameter_search_sha1_sha2_sha256_sha2:
	sub sp, sp, #480
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
	ldr x8, [x7, #0]
	ldr x9, [x7, #8]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x3, [sp, #64]
	str x4, [sp, #72]
	str x3, [sp, #88]
	str x3, [sp, #112]
	str x4, [sp, #120]
	str x5, [sp, #40]
	str x9, [sp, #136]
	movz x3, #0, lsl #0
	str x3, [sp, #80]
	str x3, [sp, #104]
	str x2, [sp, #448]
	str x7, [sp, #456]
	str x8, [sp, #464]
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
	movz x3, #32, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
24:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 25f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #32, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 27f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #32, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 29f
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
	b 210f
29:
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
210:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 214f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 215f
214:
215:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 216f
	b 217f
216:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
218:
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
	cbnz x9, 219f
	b 220f
219:
221:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 221b
220:
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
	cbnz x9, 222f
	b 223f
222:
224:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 224b
223:
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
	cbnz x9, 225f
	b 226f
225:
227:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 227b
226:
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
	cbnz x9, 228f
	b 229f
228:
230:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 230b
229:
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
	cbnz x9, 231f
	b 232f
231:
233:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 233b
232:
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
	cbnz x9, 234f
	b 235f
234:
236:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 236b
235:
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
	cbnz x9, 237f
	b 238f
237:
239:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 239b
238:
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
	cbnz x9, 240f
	b 241f
240:
242:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 242b
241:
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
	cbnz x9, 243f
	b 244f
243:
245:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 245b
244:
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
	cbnz x9, 246f
	b 247f
246:
248:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 248b
247:
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
	cbnz x9, 249f
	b 250f
249:
251:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 251b
250:
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
	cbnz x9, 252f
	b 253f
252:
254:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 254b
253:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 255f
	b 256f
255:
257:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 257b
256:
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
258:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
259:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 260f
	b 261f
260:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
261:
	cbnz x2, 259b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
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
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
263:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 264f
	b 265f
264:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
265:
	cbnz x2, 263b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
266:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
269:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
270:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
271:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 272b
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
273:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 273b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 269b
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
274:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 274b
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
275:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 275b
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
276:
	and x5, x2, x6
	cbz x5, 277f
	b 278f
277:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
278:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 276b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
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
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 282f
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
	cbz x0, 284f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 285f
284:
285:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 283f
282:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
283:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 286f
	b 287f
286:
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
	cbz x5, 288f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 289f
288:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
289:
287:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 218b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	b 291f
290:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #49152, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 292f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 293f
292:
	ldr x4, [sp, #104]
	movz x5, #49152, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
293:
291:
217:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 294f
	b 295f
294:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
295:
	b 28f
27:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
28:
	b 26f
25:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
26:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 24b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 296f
	sub x3, x3, #1
	cbz x3, 298f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 299f
298:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
299:
	b 297f
296:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #384, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2100f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2101f
2100:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2101:
297:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2102f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2104:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2104b
	movz x0, #0, lsl #0
	b 2103f
2102:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2105f
	b 2106f
2105:
2107:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2107b
2106:
	movz x0, #1, lsl #0
2103:
	ldr x0, [sp, #472]
	b 23f
22:
	movz x3, #32, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
2108:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 2109f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #32, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 2111f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #32, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 2113f
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
	b 2114f
2113:
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
2114:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 2118f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2119f
2118:
2119:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2120f
	b 2121f
2120:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2122:
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
	cbnz x9, 2123f
	b 2124f
2123:
2125:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2125b
2124:
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
	cbnz x9, 2126f
	b 2127f
2126:
2128:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2128b
2127:
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
	cbnz x9, 2129f
	b 2130f
2129:
2131:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2131b
2130:
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
	cbnz x9, 2132f
	b 2133f
2132:
2134:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2134b
2133:
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
	cbnz x9, 2135f
	b 2136f
2135:
2137:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2137b
2136:
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
	cbnz x9, 2138f
	b 2139f
2138:
2140:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2140b
2139:
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
	cbnz x9, 2141f
	b 2142f
2141:
2143:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2143b
2142:
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
	cbnz x9, 2144f
	b 2145f
2144:
2146:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2146b
2145:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2147f
	b 2148f
2147:
2149:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2149b
2148:
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
2150:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2151:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2152f
	b 2153f
2152:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2153:
	cbnz x2, 2151b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2154:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2154b
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
2155:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2156f
	b 2157f
2156:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2157:
	cbnz x2, 2155b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2158:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2159:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2160:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	lsl x6, x12, #6
2161:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2162:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2163:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2163b
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
2165:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2165b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2161b
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
2166:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2166b
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
2167:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2167b
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
2168:
	and x5, x2, x6
	cbz x5, 2169f
	b 2170f
2169:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2170:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2168b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2171:
	and x5, x2, x6
	cbz x5, 2172f
	b 2173f
2172:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2173:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2171b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2174f
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
	cbz x0, 2176f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2177f
2176:
2177:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2175f
2174:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2175:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2178f
	b 2179f
2178:
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
	cbz x5, 2180f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2181f
2180:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2181:
2179:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2122b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2182f
	b 2183f
2182:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #32768, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 2184f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 2185f
2184:
	ldr x4, [sp, #104]
	movz x5, #32768, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
2185:
2183:
2121:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2186f
	b 2187f
2186:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
2187:
	b 2112f
2111:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
2112:
	b 2110f
2109:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
2110:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2108b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 2188f
	sub x3, x3, #1
	cbz x3, 2190f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2191f
2190:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
2191:
	b 2189f
2188:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #256, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2192f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2193f
2192:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2193:
2189:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2194f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2196:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2196b
	movz x0, #0, lsl #0
	b 2195f
2194:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2197f
	b 2198f
2197:
2199:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2199b
2198:
	movz x0, #1, lsl #0
2195:
	ldr x0, [sp, #472]
23:
	b 21f
20:
	movz x3, #20, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
2200:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 2201f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #20, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 2203f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #20, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 2205f
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
	b 2206f
2205:
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
2206:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 2210f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2211f
2210:
2211:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2212f
	b 2213f
2212:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2214:
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
	cbnz x9, 2215f
	b 2216f
2215:
2217:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2217b
2216:
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
	cbnz x9, 2218f
	b 2219f
2218:
2220:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2220b
2219:
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
	cbnz x9, 2221f
	b 2222f
2221:
2223:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2223b
2222:
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
	cbnz x9, 2224f
	b 2225f
2224:
2226:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2226b
2225:
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
	cbnz x9, 2227f
	b 2228f
2227:
2229:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2229b
2228:
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
	cbnz x9, 2230f
	b 2231f
2230:
2232:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2232b
2231:
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
	cbnz x9, 2233f
	b 2234f
2233:
2235:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2235b
2234:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2236f
	b 2237f
2236:
2238:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2238b
2237:
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
2239:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2239b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2240:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2241f
	b 2242f
2241:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2242:
	cbnz x2, 2240b
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2248b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2249b
	lsl x6, x12, #6
2250:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2251:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2251b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2252:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2252b
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
2253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2253b
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
2254:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2250b
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
2255:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2255b
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
2256:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2256b
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
2257:
	and x5, x2, x6
	cbz x5, 2258f
	b 2259f
2258:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2259:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2257b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2260:
	and x5, x2, x6
	cbz x5, 2261f
	b 2262f
2261:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2262:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2260b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2263f
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
	cbz x0, 2265f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2266f
2265:
2266:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2264f
2263:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2264:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2267f
	b 2268f
2267:
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
	cbz x5, 2269f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2270f
2269:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2270:
2268:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2214b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2271f
	b 2272f
2271:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #16384, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 2273f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 2274f
2273:
	ldr x4, [sp, #104]
	movz x5, #16384, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
2274:
2272:
2213:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2275f
	b 2276f
2275:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
2276:
	b 2204f
2203:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
2204:
	b 2202f
2201:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
2202:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2200b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 2277f
	sub x3, x3, #1
	cbz x3, 2279f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2280f
2279:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
2280:
	b 2278f
2277:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #128, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2281f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2282f
2281:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2282:
2278:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2283f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2285:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2285b
	movz x0, #0, lsl #0
	b 2284f
2283:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2286f
	b 2287f
2286:
2288:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2288b
2287:
	movz x0, #1, lsl #0
2284:
	ldr x0, [sp, #472]
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
	add sp, sp, #480
	ret
	.p2align 6

vg_dsa_parameter_search:
	sub sp, sp, #480
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
	ldr x8, [x7, #0]
	ldr x9, [x7, #8]
	str x0, [sp, #48]
	str x1, [sp, #56]
	str x3, [sp, #64]
	str x4, [sp, #72]
	str x3, [sp, #88]
	str x3, [sp, #112]
	str x4, [sp, #120]
	str x5, [sp, #40]
	str x9, [sp, #136]
	movz x3, #0, lsl #0
	str x3, [sp, #80]
	str x3, [sp, #104]
	str x2, [sp, #448]
	str x7, [sp, #456]
	str x8, [sp, #464]
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
	movz x3, #32, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
24:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 25f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #32, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 27f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #32, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 29f
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
	b 210f
29:
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
210:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 214f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 215f
214:
215:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 216f
	b 217f
216:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
218:
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
	cbnz x9, 219f
	b 220f
219:
221:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 221b
220:
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
	cbnz x9, 222f
	b 223f
222:
224:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 224b
223:
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
	cbnz x9, 225f
	b 226f
225:
227:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 227b
226:
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
	cbnz x9, 228f
	b 229f
228:
230:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 230b
229:
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
	cbnz x9, 231f
	b 232f
231:
233:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 233b
232:
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
	cbnz x9, 234f
	b 235f
234:
236:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 236b
235:
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
	cbnz x9, 237f
	b 238f
237:
239:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 239b
238:
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
	cbnz x9, 240f
	b 241f
240:
242:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 242b
241:
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
	cbnz x9, 243f
	b 244f
243:
245:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 245b
244:
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
	cbnz x9, 246f
	b 247f
246:
248:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 248b
247:
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
	cbnz x9, 249f
	b 250f
249:
251:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 251b
250:
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
	cbnz x9, 252f
	b 253f
252:
254:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 254b
253:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #384, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 255f
	b 256f
255:
257:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 257b
256:
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
258:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
259:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 260f
	b 261f
260:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
261:
	cbnz x2, 259b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
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
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
263:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 264f
	b 265f
264:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
265:
	cbnz x2, 263b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
266:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
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
	lsl x6, x12, #6
269:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
270:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 270b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
271:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
272:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 272b
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
273:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 273b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 269b
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
274:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 274b
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
275:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 275b
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
276:
	and x5, x2, x6
	cbz x5, 277f
	b 278f
277:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
278:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 276b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
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
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 282f
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
	cbz x0, 284f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 285f
284:
285:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 283f
282:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
283:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 286f
	b 287f
286:
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
	cbz x5, 288f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 289f
288:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
289:
287:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 218b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 290f
	b 291f
290:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #49152, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #11264, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_3072}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 292f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 293f
292:
	ldr x4, [sp, #104]
	movz x5, #49152, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
293:
291:
217:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 294f
	b 295f
294:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
295:
	b 28f
27:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
28:
	b 26f
25:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
26:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 24b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 296f
	sub x3, x3, #1
	cbz x3, 298f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 299f
298:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
299:
	b 297f
296:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #384, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2100f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2101f
2100:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2101:
297:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2102f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2104:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2104b
	movz x0, #0, lsl #0
	b 2103f
2102:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2105f
	b 2106f
2105:
2107:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2107b
2106:
	movz x0, #1, lsl #0
2103:
	ldr x0, [sp, #472]
	b 23f
22:
	movz x3, #32, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
2108:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 2109f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #32, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 2111f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #32, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 2113f
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
	b 2114f
2113:
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
2114:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 2118f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2119f
2118:
2119:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2120f
	b 2121f
2120:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2122:
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
	cbnz x9, 2123f
	b 2124f
2123:
2125:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2125b
2124:
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
	cbnz x9, 2126f
	b 2127f
2126:
2128:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2128b
2127:
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
	cbnz x9, 2129f
	b 2130f
2129:
2131:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2131b
2130:
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
	cbnz x9, 2132f
	b 2133f
2132:
2134:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2134b
2133:
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
	cbnz x9, 2135f
	b 2136f
2135:
2137:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2137b
2136:
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
	cbnz x9, 2138f
	b 2139f
2138:
2140:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2140b
2139:
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
	cbnz x9, 2141f
	b 2142f
2141:
2143:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2143b
2142:
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
	cbnz x9, 2144f
	b 2145f
2144:
2146:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2146b
2145:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #0
	movz x9, #256, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2147f
	b 2148f
2147:
2149:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2149b
2148:
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
2150:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2150b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2151:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2152f
	b 2153f
2152:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2153:
	cbnz x2, 2151b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2154:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2154b
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
2155:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2156f
	b 2157f
2156:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2157:
	cbnz x2, 2155b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
2158:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2158b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2159:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2160:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	lsl x6, x12, #6
2161:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2162:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2163:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2163b
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
2165:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2165b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2161b
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
2166:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2166b
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
2167:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2167b
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
2168:
	and x5, x2, x6
	cbz x5, 2169f
	b 2170f
2169:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2170:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2168b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2171:
	and x5, x2, x6
	cbz x5, 2172f
	b 2173f
2172:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2173:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2171b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2174f
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
	cbz x0, 2176f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2177f
2176:
2177:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2175f
2174:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2175:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2178f
	b 2179f
2178:
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
	cbz x5, 2180f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2181f
2180:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2181:
2179:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2122b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2182f
	b 2183f
2182:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #32768, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #9216, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_2048}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 2184f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 2185f
2184:
	ldr x4, [sp, #104]
	movz x5, #32768, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
2185:
2183:
2121:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2186f
	b 2187f
2186:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
2187:
	b 2112f
2111:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
2112:
	b 2110f
2109:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
2110:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2108b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 2188f
	sub x3, x3, #1
	cbz x3, 2190f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2191f
2190:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
2191:
	b 2189f
2188:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #256, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2192f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2193f
2192:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2193:
2189:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2194f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2196:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2196b
	movz x0, #0, lsl #0
	b 2195f
2194:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2197f
	b 2198f
2197:
2199:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2199b
2198:
	movz x0, #1, lsl #0
2195:
	ldr x0, [sp, #472]
23:
	b 21f
20:
	movz x3, #20, lsl #0
	str x3, [sp, #144]
	str x3, [sp, #208]
2200:
	ldr x0, [sp, #128]
	ldr x3, [sp, #464]
	str x0, [sp, #472]
	cbz x3, 2201f
	ldr x3, [sp, #120]
	sub x3, x3, x0
	movz x4, #20, lsl #0
	subs x3, x3, x4
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	csel x3, x5, x4, hs
	cbnz x3, 2203f
	ldr x3, [sp, #112]
	str x3, [sp, #88]
	add x3, x3, x0
	str x3, [sp, #8]
	movz x4, #20, lsl #0
	add x0, x0, x4
	str x0, [sp, #128]
	movz x4, #0, lsl #0
	str x4, [sp, #104]
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
	cbz x0, 2205f
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
	b 2206f
2205:
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
2206:
	ldr x2, [sp, #0]
	ldr x12, [sp, #96]
	add x12, x12, #3328
	ldr x9, [sp, #208]
	add x13, x2, #0
	add x14, x9, #0
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
	cbz x0, 2210f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2211f
2210:
2211:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2212f
	b 2213f
2212:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	movz x3, #0, lsl #0
	str x3, [x0, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #8]
2214:
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
	cbnz x9, 2215f
	b 2216f
2215:
2217:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2217b
2216:
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
	cbnz x9, 2218f
	b 2219f
2218:
2220:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2220b
2219:
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
	cbnz x9, 2221f
	b 2222f
2221:
2223:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2223b
2222:
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
	cbnz x9, 2224f
	b 2225f
2224:
2226:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2226b
2225:
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
	cbnz x9, 2227f
	b 2228f
2227:
2229:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2229b
2228:
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
	cbnz x9, 2230f
	b 2231f
2230:
2232:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2232b
2231:
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
	cbnz x9, 2233f
	b 2234f
2233:
2235:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2235b
2234:
	ldr x2, [sp, #0]
	ldr x12, [sp, #32]
	add x12, x12, #12
	movz x9, #128, lsl #0
	add x13, x2, #0
	add x14, x9, #0
	cbnz x9, 2236f
	b 2237f
2236:
2238:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2238b
2237:
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
2239:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2239b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2240:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2241f
	b 2242f
2241:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2242:
	cbnz x2, 2240b
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
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #144]
	ldr x2, [x0, #152]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2248:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2248b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2249b
	lsl x6, x12, #6
2250:
	movz x7, #0, lsl #0
	add x14, x12, #0
	adds x3, x7, x7
	add x16, x0, #256
2251:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2251b
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x14, x12, #1
2252:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2252b
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
2253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2253b
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
2254:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	csel x4, x3, x4, hs
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2254b
	add x16, x0, #256
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x4, x4, x15
	orr x3, x3, x4
	str x3, [x16, #0]
	sub x6, x6, #1
	cbnz x6, 2250b
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
2255:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2255b
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
2256:
	ldr x3, [x16, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2256b
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
2257:
	and x5, x2, x6
	cbz x5, 2258f
	b 2259f
2258:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2259:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2257b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #168]
	ldr x9, [x0, #136]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2260:
	and x5, x2, x6
	cbz x5, 2261f
	b 2262f
2261:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2262:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2260b
	ldr x1, [x0, #160]
	ldrb w3, [x1, #0]
	lsr x3, x3, #7
	cbz x3, 2263f
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
	cbz x0, 2265f
	ldr x3, [sp, #152]
	ldr x4, [sp, #128]
	add x3, x3, x4
	str x3, [sp, #128]
	b 2266f
2265:
2266:
	lsr x3, x0, #1
	add x0, x0, x3
	str x0, [sp, #152]
	b 2264f
2263:
	movz x3, #3, lsl #0
	str x3, [sp, #152]
2264:
	ldr x0, [sp, #40]
	movz x3, #27840, lsl #0
	add x0, x0, x3
	ldr x3, [sp, #152]
	str x3, [x0, #16]
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2267f
	b 2268f
2267:
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
	cbz x5, 2269f
	movz x3, #2, lsl #0
	str x3, [x0, #16]
	b 2270f
2269:
	movz x3, #3, lsl #0
	str x3, [x0, #16]
2270:
2268:
	ldr x3, [x0, #16]
	sub x3, x3, #3
	cbz x3, 2214b
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2271f
	b 2272f
2271:
	ldr x3, [sp, #112]
	ldr x4, [sp, #128]
	ldr x6, [sp, #120]
	add x5, x3, x4
	str x5, [sp, #88]
	sub x3, x6, x4
	movz x5, #16384, lsl #0
	subs x6, x3, x5
	csel x3, x5, x3, hs
	str x3, [sp, #104]
	ldr x0, [sp, #40]
	movz x1, #7168, lsl #0
	ldr x2, [sp, #88]
	ldr x3, [sp, #104]
	bl {vg_dsa_generator_1024}
	lsr x4, x0, #2
	ldr x5, [sp, #128]
	add x5, x5, x4
	str x5, [sp, #128]
	lsl x4, x4, #2
	sub x3, x0, x4
	sub x4, x3, #3
	cbz x4, 2273f
	add x3, x3, x3
	sub x3, x3, #1
	str x3, [sp, #152]
	b 2274f
2273:
	ldr x4, [sp, #104]
	movz x5, #16384, lsl #0
	subs x4, x4, x5
	movz x4, #3, lsl #0
	movz x5, #0, lsl #0
	csel x3, x4, x5, hs
	str x3, [sp, #152]
2274:
2272:
2213:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2275f
	b 2276f
2275:
	ldr x3, [sp, #464]
	sub x3, x3, #1
	str x3, [sp, #464]
2276:
	b 2204f
2203:
	movz x3, #0, lsl #0
	str x3, [sp, #152]
2204:
	b 2202f
2201:
	movz x3, #2, lsl #0
	str x3, [sp, #152]
2202:
	ldr x0, [sp, #152]
	sub x0, x0, #3
	cbz x0, 2200b
	ldr x14, [sp, #456]
	ldr x15, [sp, #448]
	ldr x3, [sp, #152]
	cbz x3, 2277f
	sub x3, x3, #1
	cbz x3, 2279f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2280f
2279:
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #128]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #1, lsl #0
	str x9, [sp, #472]
2280:
	b 2278f
2277:
	ldr x10, [sp, #120]
	ldr x9, [sp, #472]
	sub x10, x10, x9
	movz x9, #128, lsl #0
	lsl x11, x9, #15
	add x11, x11, x9
	subs x12, x10, x11
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	csel x12, x13, x12, hs
	cbz x12, 2281f
	movz x11, #0, lsl #0
	movz x10, #0, lsl #0
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #3, lsl #0
	str x9, [sp, #472]
	b 2282f
2281:
	lsl x12, x9, #8
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	ldr x11, [sp, #464]
	ldr x12, [sp, #472]
	str x11, [x14, #0]
	str x10, [x14, #24]
	str x12, [x15, #0]
	movz x9, #0, lsl #0
	str x9, [sp, #472]
2282:
2278:
	ldr x3, [sp, #152]
	sub x3, x3, #1
	cbz x3, 2283f
	ldr x3, [sp, #48]
	str x3, [sp, #152]
	ldr x3, [sp, #56]
	str x3, [sp, #168]
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2285:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2285b
	movz x0, #0, lsl #0
	b 2284f
2283:
	ldr x12, [sp, #40]
	movz x3, #27008, lsl #0
	add x12, x12, x3
	ldr x2, [sp, #48]
	ldr x9, [sp, #56]
	cbnz x9, 2286f
	b 2287f
2286:
2288:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2288b
2287:
	movz x0, #1, lsl #0
2284:
	ldr x0, [sp, #472]
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
	add sp, sp, #480
	ret
	.p2align 6
