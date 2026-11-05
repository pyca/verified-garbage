// The functions of `src/internal/vg_rsa_pss_md5_encode.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_md5_encode:
	sub sp, sp, #336
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
	str x0, [x16, #216]
	str x2, [x16, #208]
	str x3, [x16, #224]
	str x4, [x16, #232]
	add x23, x1, #0
	add x20, x6, #0
	add x19, x20, #2048
	add x21, x20, #2304
	lsl x9, x23, #3
	sub x9, x9, x5
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
	add x9, x23, #0
	sub x10, x9, #18
	lsr x10, x10, #63
	cbnz x10, 20f
	ldr x12, [sp, #232]
	sub x9, x9, #18
	sub x10, x9, x12
	lsr x10, x10, #63
	lsr x13, x12, #63
	orr x10, x10, x13
	cbnz x10, 22f
	add x25, x9, #1
	ldr x9, [sp, #256]
	add x24, x20, #2560
	add x24, x24, x9
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
24:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 24b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #16, lsl #0
25:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #224]
	add x14, x20, #3608
	ldr x12, [sp, #232]
	cbz x12, 26f
28:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 28b
	b 27f
26:
27:
	ldr x9, [sp, #232]
	add x22, x9, #24
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
29:
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
	cbnz x12, 29b
	add x19, x20, #2296
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	str x9, [x19, #72]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
210:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
211:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 211b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 210b
	movz x27, #0, lsl #0
212:
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
	movz x12, #16, lsl #0
213:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 213b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 212b
	add x0, x20, #2240
	add x1, x21, #0
	ldr x16, [sp, #320]
	blr x16
	add x14, x20, #2560
	add x13, x23, #0
	movz x15, #0, lsl #0
214:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 214b
	add x14, x24, x25
	ldr x12, [sp, #232]
	sub x14, x14, x12
	sub x14, x14, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
	add x14, x14, #1
	ldr x11, [sp, #224]
	cbz x12, 215f
217:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 217b
	b 216f
215:
216:
	add x14, x24, x25
	add x11, x21, #0
	movz x12, #16, lsl #0
218:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 218b
	add x9, x20, #2560
	add x9, x9, x23
	sub x9, x9, #1
	movz x10, #188, lsl #0
	strb w10, [x9, #0]
	sub sp, sp, #272
	add x9, sp, #0
	add x10, x20, #512
	str x10, [x9, #96]
	add x10, x24, x25
	str x10, [x9, #104]
	movz x10, #16, lsl #0
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
219:
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
220:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 220b
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
	cbnz x12, 219b
	add sp, sp, #272
	ldrb w9, [x24, #0]
	ldr x10, [sp, #248]
	and x9, x9, x10
	strb w9, [x24, #0]
	add x11, x20, #2560
	ldr x14, [sp, #216]
	add x12, x23, #0
221:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 221b
	movz x0, #1, lsl #0
	b 23f
22:
	movz x0, #0, lsl #0
23:
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
