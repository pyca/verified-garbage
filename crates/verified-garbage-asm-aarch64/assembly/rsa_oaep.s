// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_decrypt:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #216]
	str x3, [x9, #160]
	str x4, [x9, #168]
	str x5, [x9, #176]
	str x6, [x9, #184]
	str x7, [x9, #0]
	ldr x10, [sp, #360]
	str x10, [x9, #200]
	ldr x10, [sp, #368]
	str x10, [x9, #208]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x10, [sp, #400]
	str x10, [x9, #192]
	ldr x10, [sp, #288]
	str x10, [x9, #8]
	ldr x10, [sp, #296]
	str x10, [x9, #16]
	ldr x10, [sp, #304]
	str x10, [x9, #24]
	ldr x10, [sp, #312]
	str x10, [x9, #32]
	ldr x10, [sp, #320]
	str x10, [x9, #40]
	ldr x10, [sp, #328]
	str x10, [x9, #48]
	ldr x10, [sp, #336]
	str x10, [x9, #56]
	ldr x10, [sp, #344]
	str x10, [x9, #64]
	ldr x10, [sp, #352]
	str x10, [x9, #72]
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	str x10, [x9, #80]
	str x11, [x9, #88]
	ldr x0, [sp, #96]
	add x0, x0, #0
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #376]
	ldr x7, [sp, #168]
	bl {vg_rsa_private_checked}
	ldr x16, [sp, #408]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x16, [sp, #256]
	ldr x16, [x16, #32]
	sub x17, x16, #16
	cbz x17, 20f
	sub x17, x16, #20
	cbz x17, 22f
	sub x17, x16, #28
	cbz x17, 24f
	sub x17, x16, #32
	cbz x17, 26f
	sub x17, x16, #48
	cbz x17, 28f
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #130, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 210f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #64, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #65
	ldr x13, [sp, #168]
	sub x13, x13, #65
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
212:
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
213:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 213b
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
	cbnz x12, 212b
	ldr x10, [sp, #96]
	add x10, x10, #65
	ldr x11, [sp, #168]
	sub x11, x11, #65
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #64, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
214:
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
215:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 215b
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
	cbnz x12, 214b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #65
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #64, lsl #0
216:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 216b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #129
	ldr x12, [sp, #168]
	sub x12, x12, #129
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
217:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 217b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
218:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 218b
	ldr x11, [sp, #96]
	add x11, x11, #129
	ldr x12, [sp, #168]
	sub x12, x12, #129
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
219:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 219b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
220:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
221:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 221b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 220b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
222:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 222b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #130
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 211f
210:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
223:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 223b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
211:
	b 29f
28:
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #98, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 224f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #48, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #49
	ldr x13, [sp, #168]
	sub x13, x13, #49
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
226:
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
227:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 227b
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
	cbnz x12, 226b
	ldr x10, [sp, #96]
	add x10, x10, #49
	ldr x11, [sp, #168]
	sub x11, x11, #49
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #48, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
228:
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
229:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 229b
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
	cbnz x12, 228b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #49
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #48, lsl #0
230:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 230b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #97
	ldr x12, [sp, #168]
	sub x12, x12, #97
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
231:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 231b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
232:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 232b
	ldr x11, [sp, #96]
	add x11, x11, #97
	ldr x12, [sp, #168]
	sub x12, x12, #97
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
233:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 233b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
234:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
235:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 235b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 234b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
236:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 236b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #98
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 225f
224:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
237:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 237b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
225:
29:
	b 27f
26:
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #66, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 238f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #32, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #33
	ldr x13, [sp, #168]
	sub x13, x13, #33
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
240:
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
241:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 241b
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
	cbnz x12, 240b
	ldr x10, [sp, #96]
	add x10, x10, #33
	ldr x11, [sp, #168]
	sub x11, x11, #33
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #32, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
242:
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
243:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 243b
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
	cbnz x12, 242b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #33
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #32, lsl #0
244:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 244b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #65
	ldr x12, [sp, #168]
	sub x12, x12, #65
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
245:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 245b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
246:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 246b
	ldr x11, [sp, #96]
	add x11, x11, #65
	ldr x12, [sp, #168]
	sub x12, x12, #65
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
247:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 247b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
248:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
249:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 249b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 248b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
250:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 250b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #66
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 239f
238:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
251:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 251b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
239:
27:
	b 25f
24:
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 252f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
254:
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
255:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 255b
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
	cbnz x12, 254b
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
256:
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
257:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 257b
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
	cbnz x12, 256b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #28, lsl #0
258:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 258b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
259:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 259b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
260:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 260b
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
261:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 261b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
262:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
263:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 263b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 262b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
264:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 264b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 253f
252:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
265:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 265b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
253:
25:
	b 23f
22:
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #42, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 266f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #20, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #21
	ldr x13, [sp, #168]
	sub x13, x13, #21
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
268:
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
269:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 269b
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
	cbnz x12, 268b
	ldr x10, [sp, #96]
	add x10, x10, #21
	ldr x11, [sp, #168]
	sub x11, x11, #21
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #20, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
270:
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
271:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 271b
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
	cbnz x12, 270b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #21
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #20, lsl #0
272:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 272b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #41
	ldr x12, [sp, #168]
	sub x12, x12, #41
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
273:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 273b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
274:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 274b
	ldr x11, [sp, #96]
	add x11, x11, #41
	ldr x12, [sp, #168]
	sub x12, x12, #41
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
275:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 275b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
276:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
277:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 277b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 276b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
278:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 278b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #42
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 267f
266:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
279:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 279b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
267:
23:
	b 21f
20:
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #34, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 280f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #16, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #17
	ldr x13, [sp, #168]
	sub x13, x13, #17
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
282:
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
283:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 283b
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
	cbnz x12, 282b
	ldr x10, [sp, #96]
	add x10, x10, #17
	ldr x11, [sp, #168]
	sub x11, x11, #17
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #16, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #416]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
284:
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
285:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 285b
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
	cbnz x12, 284b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #17
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #16, lsl #0
286:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 286b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #33
	ldr x12, [sp, #168]
	sub x12, x12, #33
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
287:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 287b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
288:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 288b
	ldr x11, [sp, #96]
	add x11, x11, #33
	ldr x12, [sp, #168]
	sub x12, x12, #33
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
289:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 289b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
290:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
291:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 291b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 290b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
292:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 292b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #34
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 281f
280:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
293:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 293b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
281:
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_rsa_oaep_encrypt_precomputed:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #160]
	str x3, [x9, #168]
	str x4, [x9, #176]
	str x5, [x9, #184]
	str x6, [x9, #200]
	str x7, [x9, #208]
	ldr x10, [sp, #288]
	str x10, [x9, #216]
	ldr x10, [sp, #296]
	str x10, [x9, #224]
	ldr x10, [sp, #304]
	str x10, [x9, #232]
	ldr x10, [sp, #320]
	str x10, [x9, #96]
	ldr x10, [sp, #328]
	str x10, [x9, #192]
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x16, [sp, #256]
	ldr x16, [x16, #32]
	sub x17, x16, #16
	cbz x17, 20f
	sub x17, x16, #20
	cbz x17, 22f
	sub x17, x16, #28
	cbz x17, 24f
	sub x17, x16, #32
	cbz x17, 26f
	sub x17, x16, #48
	cbz x17, 28f
	ldr x10, [sp, #168]
	movz x12, #130, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 210f
	ldr x10, [sp, #168]
	sub x10, x10, #130
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 212f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
214:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 214b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #64, lsl #0
215:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 215b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #65
	movz x13, #64, lsl #0
216:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 216b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 217f
	b 218f
217:
219:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 219b
218:
	ldr x10, [sp, #96]
	add x10, x10, #65
	ldr x11, [sp, #168]
	sub x11, x11, #65
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #64, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
220:
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
221:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 221b
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
	cbnz x12, 220b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #64, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #65
	ldr x13, [sp, #168]
	sub x13, x13, #65
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
222:
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
223:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 223b
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
	cbnz x12, 222b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 213f
212:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
224:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 224b
	movz x0, #0, lsl #0
213:
	b 211f
210:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
225:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 225b
	movz x0, #0, lsl #0
211:
	b 29f
28:
	ldr x10, [sp, #168]
	movz x12, #98, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 226f
	ldr x10, [sp, #168]
	sub x10, x10, #98
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 228f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
230:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 230b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #48, lsl #0
231:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 231b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #49
	movz x13, #48, lsl #0
232:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 232b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 233f
	b 234f
233:
235:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 235b
234:
	ldr x10, [sp, #96]
	add x10, x10, #49
	ldr x11, [sp, #168]
	sub x11, x11, #49
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #48, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
236:
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
237:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 237b
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
	cbnz x12, 236b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #48, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #49
	ldr x13, [sp, #168]
	sub x13, x13, #49
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
238:
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
239:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 239b
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
	cbnz x12, 238b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 229f
228:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
240:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 240b
	movz x0, #0, lsl #0
229:
	b 227f
226:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
241:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 241b
	movz x0, #0, lsl #0
227:
29:
	b 27f
26:
	ldr x10, [sp, #168]
	movz x12, #66, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 242f
	ldr x10, [sp, #168]
	sub x10, x10, #66
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 244f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
246:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 246b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #32, lsl #0
247:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 247b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #33
	movz x13, #32, lsl #0
248:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 248b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 249f
	b 250f
249:
251:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 251b
250:
	ldr x10, [sp, #96]
	add x10, x10, #33
	ldr x11, [sp, #168]
	sub x11, x11, #33
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #32, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
252:
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
253:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 253b
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
	cbnz x12, 252b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #32, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #33
	ldr x13, [sp, #168]
	sub x13, x13, #33
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
254:
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
255:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 255b
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
	cbnz x12, 254b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 245f
244:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
256:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 256b
	movz x0, #0, lsl #0
245:
	b 243f
242:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
257:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 257b
	movz x0, #0, lsl #0
243:
27:
	b 25f
24:
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 258f
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 260f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
262:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 262b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
263:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 263b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #29
	movz x13, #28, lsl #0
264:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 264b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 265f
	b 266f
265:
267:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 267b
266:
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
268:
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
269:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 269b
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
	cbnz x12, 268b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
270:
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
271:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 271b
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
	cbnz x12, 270b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 261f
260:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
272:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 272b
	movz x0, #0, lsl #0
261:
	b 259f
258:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
273:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 273b
	movz x0, #0, lsl #0
259:
25:
	b 23f
22:
	ldr x10, [sp, #168]
	movz x12, #42, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 274f
	ldr x10, [sp, #168]
	sub x10, x10, #42
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 276f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
278:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 278b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #20, lsl #0
279:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 279b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #21
	movz x13, #20, lsl #0
280:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 280b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 281f
	b 282f
281:
283:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 283b
282:
	ldr x10, [sp, #96]
	add x10, x10, #21
	ldr x11, [sp, #168]
	sub x11, x11, #21
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #20, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
284:
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
285:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 285b
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
	cbnz x12, 284b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #20, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #21
	ldr x13, [sp, #168]
	sub x13, x13, #21
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
286:
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
287:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 287b
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
	cbnz x12, 286b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 277f
276:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
288:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 288b
	movz x0, #0, lsl #0
277:
	b 275f
274:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
289:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 289b
	movz x0, #0, lsl #0
275:
23:
	b 21f
20:
	ldr x10, [sp, #168]
	movz x12, #34, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 290f
	ldr x10, [sp, #168]
	sub x10, x10, #34
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 292f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
294:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 294b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #16, lsl #0
295:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 295b
	ldr x16, [sp, #352]
	add x9, sp, #0
	str x16, [x9, #256]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x16, [sp, #256]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	ldr x16, [sp, #256]
	ldr x16, [x16, #16]
	blr x16
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #17
	movz x13, #16, lsl #0
296:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 296b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 297f
	b 298f
297:
299:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 299b
298:
	ldr x10, [sp, #96]
	add x10, x10, #17
	ldr x11, [sp, #168]
	sub x11, x11, #17
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #16, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
2100:
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
2101:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 2101b
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
	cbnz x12, 2100b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #16, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #17
	ldr x13, [sp, #168]
	sub x13, x13, #17
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	ldr x10, [sp, #360]
	add x9, sp, #0
	str x10, [x9, #256]
	ldr x10, [x10, #32]
	add x9, sp, #0
	str x10, [x9, #264]
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
2102:
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
2103:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 2103b
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
	cbnz x12, 2102b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #336]
	ldr x3, [sp, #344]
	bl {vg_rsa_public_precomputed_checked}
	b 293f
292:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2104:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2104b
	movz x0, #0, lsl #0
293:
	b 291f
290:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
2105:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 2105b
	movz x0, #0, lsl #0
291:
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.p2align 6
