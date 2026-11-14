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
2130:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2131:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2132f
	b 2133f
2132:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2133:
	cbnz x2, 2131b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2134:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2134b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2135:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2135b
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
2136:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2140:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
2141:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2141b
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
2142:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2143f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2145f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2147:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2148:
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
	cbnz x13, 2148b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2149:
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
2150:
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
	cbnz x14, 2150b
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2149b
	b 2146f
2145:
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
2146:
	b 2144f
2143:
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
2144:
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
	ldr x3, [x0, #200]
	str x3, [x0, #208]
	movz x3, #0, lsl #0
	str x3, [x0, #224]
2178:
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
2179:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2179b
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
	cbnz x4, 2178b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
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
2180:
	and x5, x2, x6
	cbz x5, 2181f
	b 2182f
2181:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2182:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2180b
	ldr x0, [x0, #128]
	movz x3, #14944, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x3, [x0, #280]
	add x2, x3, #0
	ldr x9, [x0, #328]
	movz x8, #0, lsl #0
2183:
	ldrb w3, [x1, #0]
	ldrb w10, [x2, #0]
	eor x3, x3, x10
	orr x8, x8, x3
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2183b
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
2130:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2130b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2131f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2133f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2135:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2136:
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
	cbnz x13, 2136b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2137:
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
2138:
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
	cbnz x14, 2138b
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2137b
	b 2134f
2133:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2140f
2142:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2142b
	b 2141f
2140:
2141:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2143:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2144:
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
2145:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2144b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2148:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2148b
2134:
	b 2132f
2131:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2149:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2149b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2150:
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
2151:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2151b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2150b
2132:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2154:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
2158:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2158b
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
2159:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2159b
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
2160:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2161:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2162:
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
	cbnz x3, 2162b
2164:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2165:
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
	cbz x3, 2166f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2168:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2168b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2167f
2166:
2167:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2165b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2164b
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
2169:
	and x5, x2, x6
	cbz x5, 2170f
	b 2171f
2170:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2171:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2169b
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
2172:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2172b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2173:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2174f
	b 2175f
2174:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2175:
	cbnz x2, 2173b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2176:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2176b
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
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
267:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 268f
	b 269f
268:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
269:
	cbnz x2, 267b
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
270:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 270b
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
271:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 271b
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
272:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 272b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
273:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 273b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
274:
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
275:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 275b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 274b
276:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
277:
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
278:
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
279:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
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
	cbnz x4, 278b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 277b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 276b
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
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2107:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2107b
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
2108:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2109:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2110f
2112:
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
2113:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
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
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2112b
	b 2111f
2110:
2111:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2116:
	and x5, x2, x6
	cbz x5, 2117f
	b 2118f
2117:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2118:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2116b
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
2119:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2120f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2122f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2124:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2125:
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
	cbnz x13, 2125b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2126:
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
2127:
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
	cbnz x14, 2127b
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
2128:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2128b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2126b
	b 2123f
2122:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2129f
2131:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2131b
	b 2130f
2129:
2130:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2132:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2133:
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
2134:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2134b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2135:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2136:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2133b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2137:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2137b
2123:
	b 2121f
2120:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
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
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2139:
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
2140:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2141:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2141b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2142:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2139b
2121:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2143:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2144:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2145f
	b 2146f
2145:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2146:
	cbnz x2, 2144b
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2147:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2147b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2148:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2149f
	b 2150f
2149:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2150:
	cbnz x2, 2148b
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
2151:
	and x5, x2, x6
	cbz x5, 2152f
	b 2153f
2152:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2153:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2151b
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
2154:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2154b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2155f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2157f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2159:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2159b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2160:
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
	cbnz x13, 2160b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2161:
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
2162:
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
	cbnz x14, 2162b
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
2163:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2161b
	b 2158f
2157:
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
2158:
	b 2156f
2155:
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
2156:
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
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2182:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2182b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2183:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2184f
	b 2185f
2184:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2185:
	cbnz x2, 2183b
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
2186:
	and x5, x2, x6
	cbz x5, 2187f
	b 2188f
2187:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2188:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2186b
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
2189:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2189b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2190f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2192f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2194:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2194b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2195:
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
	cbnz x13, 2195b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2196:
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
2197:
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
	cbnz x14, 2197b
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
2198:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2198b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2196b
	b 2193f
2192:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2199f
2201:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2201b
	b 2200f
2199:
2200:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2202:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2202b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2203:
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
2204:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2204b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2205:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2205b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2206:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2206b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2203b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2207:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2207b
2193:
	b 2191f
2190:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2208:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2208b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2209:
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
2210:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2210b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2211b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2212:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2212b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2209b
2191:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2213:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2213b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
	ldr x8, [x0, #104]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2217:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2217b
	ldr x5, [x0, #128]
	ldr x1, [x5, #144]
	ldr x2, [x5, #152]
	ldr x8, [x0, #104]
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
2221:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2221b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #120]
	add x14, x12, #0
2222:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2222b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #72]
	add x14, x12, #0
2223:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2223b
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
2224:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2224b
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
2225:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2225b
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
2226:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2226b
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
2227:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2227b
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
2228:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2228b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2229:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2229b
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
2230:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2230b
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
2231:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2231b
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
2232:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2232b
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
2233:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2233b
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
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2235:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2235b
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
2236:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2236b
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
2237:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2237b
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
2238:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2238b
	ldr x12, [x0, #48]
	ldr x16, [x0, #112]
	ldr x17, [x0, #208]
	add x14, x12, #0
2239:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2239b
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
2240:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2240b
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
2241:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2241b
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
2242:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
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
	mov v31.d[0], x30
	bl {vg_rsa_mul_1_1_4}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x17, [x0, #112]
	add x14, x12, #0
2243:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2243b
	ldr x12, [x0, #48]
	ldr x16, [x0, #120]
	ldr x17, [x0, #112]
	add x14, x12, #0
2244:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2244b
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2245b
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
2246:
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
2247:
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
2248:
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
2249:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
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
	ldr x3, [x0, #224]
	add x3, x3, #1
	str x3, [x0, #224]
	sub x4, x3, #16
	cbnz x4, 2248b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2247b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2246b
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
2250:
	and x5, x2, x6
	cbz x5, 2251f
	b 2252f
2251:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2252:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2250b
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
2253:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2253b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2254f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2256f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2258:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2258b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2259:
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
	cbnz x13, 2259b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2260:
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
2261:
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
	cbnz x14, 2261b
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
2262:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2262b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2260b
	b 2257f
2256:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2263f
2265:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2265b
	b 2264f
2263:
2264:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2266b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2267:
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
2268:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2268b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2269:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2269b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2270:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2270b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2267b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2271:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2271b
2257:
	b 2255f
2254:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2272:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2272b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2273:
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
2274:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2274b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2275:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2275b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2276:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2276b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2273b
2255:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2277b
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
2278:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2278b
	ldr x8, [x0, #72]
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
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2280f
2282:
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
2283:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2283b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2284:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2284b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2285:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2285b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2282b
	b 2281f
2280:
2281:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
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
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x3, [x0, #296]
	add x2, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
2289:
	ldrb w3, [x1, #0]
	ldrb w10, [x2, #0]
	eor x3, x3, x10
	orr x8, x8, x3
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2289b
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
240:
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
	cbnz x14, 240b
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
	cbz x6, 242f
244:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 244b
	b 243f
242:
243:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
245:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 245b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
246:
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
247:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 247b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 246b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
250:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 250b
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
251:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 251b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
252:
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
253:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 253b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 252b
234:
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
256:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
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
260:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 260b
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
	movz x3, #14, lsl #0
	str x3, [x0, #160]
264:
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
265:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 264b
266:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
267:
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
268:
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
	cbnz x4, 268b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 267b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 266b
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
270:
	and x5, x2, x6
	cbz x5, 271f
	b 272f
271:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
272:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 270b
	ldr x0, [x0, #128]
	movz x3, #15328, lsl #0
	add x1, x0, x3
	movz x3, #15712, lsl #0
	add x2, x0, x3
	ldr x9, [x0, #328]
	movz x8, #0, lsl #0
	sub x8, x8, #1
273:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 273b
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
274:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 274b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
275:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 276f
	b 277f
276:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
277:
	cbnz x2, 275b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
278:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
279:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 279b
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
280:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 280b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
281:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 282f
	b 283f
282:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
283:
	cbnz x2, 281b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	lsr x15, x15, #1
	add x16, x16, #8
	sub x14, x12, #1
284:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 284b
	ldr x16, [x0, #72]
	ldr x17, [x0, #64]
	ldr x14, [x0, #48]
	movz x7, #0, lsl #0
	subs x3, x7, x7
285:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 285b
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
286:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 286b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
287:
	and x5, x2, x6
	cbz x5, 288f
	b 289f
288:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
289:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 287b
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
290:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 290b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 291f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 293f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
295:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 295b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
296:
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
	cbnz x13, 296b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
297:
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
298:
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
	cbnz x14, 298b
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 297b
	b 294f
293:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2100f
2102:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2102b
	b 2101f
2100:
2101:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2103:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2103b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2104:
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
2105:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	adc x3, x7, x7
	str x3, [x16, #0]
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
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2104b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2108:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2108b
294:
	b 292f
291:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2109:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
2110:
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
2111:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2112:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2113:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2110b
292:
	ldr x12, [x0, #48]
	movz x9, #256, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #72]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2114:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2114b
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
2115:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x8, [x0, #72]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2116:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x3, [x5, #136]
	str x1, [x0, #184]
	str x3, [x0, #176]
	cbz x3, 2117f
2119:
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
2120:
	ldr x3, [x9, #0]
	ldr x4, [x17, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x9, x9, #8
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2121:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2122:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	ldr x3, [x0, #176]
	sub x3, x3, #1
	str x3, [x0, #176]
	cbnz x3, 2119b
	b 2118f
2117:
2118:
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
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
	ldr x0, [x0, #128]
	movz x3, #14816, lsl #0
	add x3, x0, x3
	add x1, x3, #0
	ldr x9, [x0, #336]
	movz x8, #0, lsl #0
2126:
	ldrb w3, [x1, #0]
	orr x8, x8, x3
	add x1, x1, #1
	sub x9, x9, #1
	cbnz x9, 2126b
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
2127:
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	ldr x5, [x0, #128]
	ldr x1, [x5, #160]
	ldr x9, [x5, #168]
	add x1, x1, x9
	ldr x8, [x0, #112]
	movz x15, #0, lsl #0
	sub x15, x15, #1
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2128:
	and x5, x2, x6
	cbz x5, 2129f
	b 2130f
2129:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2130:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2128b
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
2131:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2131b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 2132f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2134f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2136:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2137:
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
	cbnz x13, 2137b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2138:
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
2139:
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
	cbnz x14, 2139b
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
2140:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2138b
	b 2135f
2134:
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
2135:
	b 2133f
2132:
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
2133:
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
2159:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2159b
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
2160:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2160b
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
2161:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2161b
	ldr x12, [x0, #48]
	ldr x16, [x0, #96]
	ldr x17, [x0, #104]
	add x14, x12, #0
2162:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2162b
	movz x3, #14, lsl #0
	str x3, [x0, #160]
2163:
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
2164:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2164b
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2163b
2165:
	ldr x3, [x0, #136]
	ldr x4, [x0, #152]
	add x3, x3, x4
	ldrb w3, [x3, #0]
	str x3, [x0, #168]
	movz x3, #2, lsl #0
	str x3, [x0, #160]
2166:
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
	cbz x3, 2167f
	ldr x12, [x0, #48]
	add x4, x12, #2
	ldr x3, [x0, #216]
	mul x4, x4, x3
	lsl x4, x4, #3
	ldr x16, [x0, #200]
	add x16, x16, x4
	ldr x17, [x0, #104]
	add x14, x12, #0
2169:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2169b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	b 2168f
2167:
2168:
	ldr x3, [x0, #160]
	sub x3, x3, #1
	str x3, [x0, #160]
	cbnz x3, 2166b
	ldr x3, [x0, #152]
	add x3, x3, #1
	str x3, [x0, #152]
	ldr x4, [x0, #144]
	sub x3, x4, x3
	cbnz x3, 2165b
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
2170:
	and x5, x2, x6
	cbz x5, 2171f
	b 2172f
2171:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2172:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2170b
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
2173:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2173b
	ldr x5, [x0, #128]
	ldr x1, [x5, #128]
	ldr x2, [x5, #136]
	ldr x8, [x0, #72]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2174:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2175f
	b 2176f
2175:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2176:
	cbnz x2, 2174b
	ldr x12, [x0, #48]
	ldr x16, [x0, #72]
	ldr x15, [x16, #0]
	movz x3, #1, lsl #0
	eor x15, x15, x3
	add x16, x16, #8
	sub x14, x12, #1
2177:
	ldr x3, [x16, #0]
	orr x15, x15, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2177b
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
2178:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2178b
	add x2, x10, x13
	add x2, x2, x13
	add x2, x2, x14
	add x1, x11, #0
	add x9, x13, #0
2179:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2179b
	add x2, x10, x13
	add x2, x2, x13
	add x2, x2, x13
	add x2, x2, x14
	add x1, x12, #0
	add x9, x14, #0
2180:
	ldrb w3, [x1, #0]
	and x3, x3, x8
	strb w3, [x2, #0]
	add x1, x1, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2180b
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
2181:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 2181b
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
