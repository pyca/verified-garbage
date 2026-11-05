// The functions of `src/internal/vg_rsa_pss_sha224_check_encoding.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha224_check_encoding:
	sub sp, sp, #336
	add w5, w5, #0
	add x16, sp, #0
	str x19, [x16, #96]
	str x20, [x16, #104]
	str x21, [x16, #112]
	str x22, [x16, #120]
	str x23, [x16, #128]
	str x24, [x16, #136]
	str x25, [x16, #144]
	str x26, [x16, #152]
	str x27, [x16, #160]
	str x28, [x16, #168]
	str x30, [x16, #176]
	str x0, [x16, #208]
	str x4, [x16, #232]
	str x5, [x16, #264]
	add x23, x2, #0
	add x20, x6, #0
	add x19, x20, #2048
	add x21, x20, #2304
	lsl x9, x23, #3
	sub x9, x9, x3
	movz x11, #0, lsl #0
	sub x12, x9, #8
	lsr x12, x12, #63
	lsl x12, x12, #0
	orr x11, x11, x12
	sub x12, x9, #7
	lsr x12, x12, #63
	lsl x12, x12, #1
	orr x11, x11, x12
	sub x12, x9, #6
	lsr x12, x12, #63
	lsl x12, x12, #2
	orr x11, x11, x12
	sub x12, x9, #5
	lsr x12, x12, #63
	lsl x12, x12, #3
	orr x11, x11, x12
	sub x12, x9, #4
	lsr x12, x12, #63
	lsl x12, x12, #4
	orr x11, x11, x12
	sub x12, x9, #3
	lsr x12, x12, #63
	lsl x12, x12, #5
	orr x11, x11, x12
	sub x12, x9, #2
	lsr x12, x12, #63
	lsl x12, x12, #6
	orr x11, x11, x12
	sub x12, x9, #1
	lsr x12, x12, #63
	lsl x12, x12, #7
	orr x11, x11, x12
	add x16, sp, #0
	str x11, [x16, #248]
	movz x12, #0, lsl #0
	add x16, sp, #0
	str x12, [x16, #256]
	ldr x9, [sp, #336]
	ldr x10, [x9, #0]
	add x16, sp, #0
	str x10, [x16, #296]
	ldr x10, [x9, #24]
	add x16, sp, #0
	str x10, [x16, #312]
	ldr x10, [x9, #32]
	add x16, sp, #0
	str x10, [x16, #320]
	ldr x9, [sp, #344]
	add x16, sp, #0
	str x9, [x16, #288]
	add x11, x1, #0
	add x14, x20, #2560
	add x12, x23, #0
20:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 20b
	add x9, x23, #0
	sub x10, x9, #30
	lsr x10, x10, #63
	cbnz x10, 21f
	ldr x13, [sp, #264]
	cbz x13, 23f
	movz x12, #0, lsl #0
	b 24f
23:
	ldr x12, [sp, #232]
24:
	sub x9, x9, #30
	sub x10, x9, x12
	lsr x10, x10, #63
	lsr x13, x12, #63
	orr x10, x10, x13
	cbnz x10, 25f
	add x25, x9, #1
	ldr x9, [sp, #256]
	add x24, x20, #2560
	add x24, x24, x9
	add x10, x20, #2560
	add x9, x10, x23
	sub x9, x9, #1
	ldrb w26, [x9, #0]
	movz x9, #188, lsl #0
	eor x26, x26, x9
	ldrb w11, [x10, #0]
	ldr x12, [sp, #256]
	movz x9, #0, lsl #0
	sub x12, x9, x12
	and x11, x11, x12
	orr x26, x26, x11
	ldrb w11, [x24, #0]
	ldr x12, [sp, #248]
	movz x9, #255, lsl #0
	eor x12, x12, x9
	and x11, x11, x12
	orr x26, x26, x11
	sub sp, sp, #272
	add x9, sp, #0
	add x10, x20, #512
	str x10, [x9, #96]
	add x10, x24, x25
	str x10, [x9, #104]
	movz x10, #28, lsl #0
	str x10, [x9, #112]
	str x24, [x9, #120]
	str x25, [x9, #128]
	ldr x10, [sp, #560]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
27:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	ldr x14, [sp, #264]
	subs x15, x13, x14
	csel x14, x14, x13, hs
28:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 28b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	ldr x13, [sp, #264]
	add x10, x10, x13
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 27b
	add sp, sp, #272
	ldrb w9, [x24, #0]
	ldr x10, [sp, #248]
	and x9, x9, x10
	strb w9, [x24, #0]
	add x10, x24, #0
	movz x11, #0, lsl #0
	add x12, x25, #0
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
29:
	ldrb w9, [x10, #0]
	sub x8, x9, #1
	lsr x8, x8, #63
	sub x16, x8, #1
	and x16, x16, x13
	and x17, x11, x16
	orr x14, x14, x17
	and x17, x9, x16
	orr x15, x15, x17
	movz x17, #0, lsl #0
	sub x17, x17, x8
	and x13, x13, x17
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 29b
	movz x9, #1, lsl #0
	eor x15, x15, x9
	lsr x13, x13, #63
	orr x15, x15, x13
	orr x26, x26, x15
	add x16, sp, #0
	str x14, [x16, #304]
	sub x11, x25, x14
	sub x11, x11, #1
	ldr x9, [sp, #264]
	cbz x9, 210f
	b 211f
210:
	ldr x12, [sp, #232]
	eor x12, x12, x11
	orr x26, x26, x12
211:
	ldr x9, [sp, #264]
	cbz x9, 212f
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
214:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 214b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #28, lsl #0
215:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 215b
	add x11, x24, #0
	add x14, x20, #3620
	add x12, x25, #0
216:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 216b
	ldr x27, [sp, #304]
	add x27, x27, #1
	movz x28, #1, lsl #0
	movz x22, #10, lsl #0
217:
	add x10, x20, #3620
	add x11, x10, x28
	lsr x14, x27, #1
	lsl x14, x14, #1
	sub x14, x27, x14
	movz x9, #0, lsl #0
	sub x14, x9, x14
	add x12, x25, #0
218:
	ldrb w15, [x10, #0]
	ldrb w9, [x11, #0]
	eor x9, x9, x15
	and x9, x9, x14
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 218b
	lsr x27, x27, #1
	add x28, x28, x28
	sub x22, x22, #1
	cbnz x22, 217b
	ldr x9, [sp, #304]
	sub x9, x25, x9
	sub x9, x9, #1
	add x22, x9, #36
	add x9, x25, #43
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	ldr x16, [sp, #296]
	blr x16
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
219:
	ldrb w13, [x10, #0]
	eor x14, x11, x22
	sub x14, x14, #1
	lsr x14, x14, #63
	lsl x14, x14, #7
	orr x13, x13, x14
	strb w13, [x10, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 219b
	add x19, x20, #2280
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
220:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
221:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 221b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 220b
	movz x27, #0, lsl #0
222:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	ldr x16, [sp, #312]
	blr x16
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #32, lsl #0
223:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 223b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 222b
	add x0, x20, #2240
	add x1, x21, #0
	ldr x16, [sp, #320]
	blr x16
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #28, lsl #0
224:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 224b
	sub x0, x26, #1
	lsr x0, x0, #63
	b 213f
212:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
225:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 225b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #28, lsl #0
226:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 226b
	add x11, x24, x25
	ldr x12, [sp, #232]
	sub x11, x11, x12
	add x14, x20, #3620
	cbz x12, 227f
229:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 229b
	b 228f
227:
228:
	ldr x9, [sp, #232]
	add x22, x9, #36
	add x9, x22, #8
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	ldr x16, [sp, #296]
	blr x16
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
230:
	ldrb w13, [x10, #0]
	eor x14, x11, x22
	sub x14, x14, #1
	lsr x14, x14, #63
	lsl x14, x14, #7
	orr x13, x13, x14
	strb w13, [x10, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 230b
	add x19, x20, #2280
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
231:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
232:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 232b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 231b
	movz x27, #0, lsl #0
233:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	ldr x16, [sp, #312]
	blr x16
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #32, lsl #0
234:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 234b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 233b
	add x0, x20, #2240
	add x1, x21, #0
	ldr x16, [sp, #320]
	blr x16
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #28, lsl #0
235:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 235b
	sub x0, x26, #1
	lsr x0, x0, #63
213:
	b 26f
25:
	movz x0, #0, lsl #0
26:
	b 22f
21:
	movz x0, #0, lsl #0
22:
	add x16, sp, #0
	ldr x19, [x16, #96]
	ldr x20, [x16, #104]
	ldr x21, [x16, #112]
	ldr x22, [x16, #120]
	ldr x23, [x16, #128]
	ldr x24, [x16, #136]
	ldr x25, [x16, #144]
	ldr x26, [x16, #152]
	ldr x27, [x16, #160]
	ldr x28, [x16, #168]
	ldr x30, [x16, #176]
	add sp, sp, #336
	ret
	.p2align 6
