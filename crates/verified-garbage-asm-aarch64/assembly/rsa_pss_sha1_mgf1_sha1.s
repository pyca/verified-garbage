// The functions of `src/rsa_pss_sha1_mgf1_sha1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha1_mgf1_sha1_encode:
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
	add x9, x23, #0
	sub x10, x9, #22
	lsr x10, x10, #63
	cbnz x10, 20f
	ldr x12, [sp, #232]
	sub x9, x9, #22
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
	movz x12, #20, lsl #0
25:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #224]
	add x14, x20, #3612
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
	add x22, x9, #28
	add x9, x22, #8
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
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
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
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
	bl {vg_sha1_compress}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
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
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
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
	movz x12, #20, lsl #0
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
	movz x28, #0, lsl #0
	movz x9, #0, lsl #0
	add x16, sp, #0
	str x9, [x16, #272]
219:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #8, lsl #0
220:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 220b
	add x11, x24, x25
	add x14, x20, #3584
	movz x12, #20, lsl #0
221:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 221b
	add x10, x20, #3604
	lsr x9, x28, #24
	strb w9, [x10, #0]
	lsr x9, x28, #16
	strb w9, [x10, #1]
	lsr x9, x28, #8
	strb w9, [x10, #2]
	strb w28, [x10, #3]
	movz x22, #24, lsl #0
	movz x9, #1, lsl #0
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3608
	ldrb w9, [x10, #0]
	movz x13, #128, lsl #0
	orr x9, x9, x13
	strb w9, [x10, #0]
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
222:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
223:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 223b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 222b
	movz x27, #0, lsl #0
224:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
225:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 225b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 224b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	ldr x9, [sp, #272]
	add x10, x24, x9
	add x11, x21, #0
	sub x12, x25, x9
	movz x13, #20, lsl #0
	sub x14, x12, x13
	lsr x14, x14, #63
	cbz x14, 226f
	b 227f
226:
	add x12, x13, #0
227:
228:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 228b
	add x28, x28, #1
	ldr x9, [sp, #272]
	add x9, x9, #20
	add x16, sp, #0
	str x9, [x16, #272]
	sub x10, x9, x25
	lsr x10, x10, #63
	cbnz x10, 219b
	ldrb w9, [x24, #0]
	ldr x10, [sp, #248]
	and x9, x9, x10
	strb w9, [x24, #0]
	add x11, x20, #2560
	ldr x14, [sp, #216]
	add x12, x23, #0
229:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 229b
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

vg_rsa_pss_sha1_mgf1_sha1_check_encoding:
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
	sub x10, x9, #22
	lsr x10, x10, #63
	cbnz x10, 21f
	ldr x13, [sp, #264]
	cbz x13, 23f
	movz x12, #0, lsl #0
	b 24f
23:
	ldr x12, [sp, #232]
24:
	sub x9, x9, #22
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
	movz x28, #0, lsl #0
	movz x9, #0, lsl #0
	add x16, sp, #0
	str x9, [x16, #272]
27:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #8, lsl #0
28:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 28b
	add x11, x24, x25
	add x14, x20, #3584
	movz x12, #20, lsl #0
29:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 29b
	add x10, x20, #3604
	lsr x9, x28, #24
	strb w9, [x10, #0]
	lsr x9, x28, #16
	strb w9, [x10, #1]
	lsr x9, x28, #8
	strb w9, [x10, #2]
	strb w28, [x10, #3]
	movz x22, #24, lsl #0
	movz x9, #1, lsl #0
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3608
	ldrb w9, [x10, #0]
	movz x13, #128, lsl #0
	orr x9, x9, x13
	strb w9, [x10, #0]
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
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
	bl {vg_sha1_compress}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
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
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	ldr x9, [sp, #272]
	add x10, x24, x9
	add x11, x21, #0
	sub x12, x25, x9
	movz x13, #20, lsl #0
	sub x14, x12, x13
	lsr x14, x14, #63
	cbz x14, 214f
	b 215f
214:
	add x12, x13, #0
215:
216:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 216b
	add x28, x28, #1
	ldr x9, [sp, #272]
	add x9, x9, #20
	add x16, sp, #0
	str x9, [x16, #272]
	sub x10, x9, x25
	lsr x10, x10, #63
	cbnz x10, 27b
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
217:
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
	cbnz x12, 217b
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
	cbz x9, 218f
	b 219f
218:
	ldr x12, [sp, #232]
	eor x12, x12, x11
	orr x26, x26, x12
219:
	ldr x9, [sp, #264]
	cbz x9, 220f
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
222:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 222b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #20, lsl #0
223:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 223b
	add x11, x24, #0
	add x14, x20, #3612
	add x12, x25, #0
224:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 224b
	ldr x27, [sp, #304]
	add x27, x27, #1
	movz x28, #1, lsl #0
	movz x22, #10, lsl #0
225:
	add x10, x20, #3612
	add x11, x10, x28
	lsr x14, x27, #1
	lsl x14, x14, #1
	sub x14, x27, x14
	movz x9, #0, lsl #0
	sub x14, x9, x14
	add x12, x25, #0
226:
	ldrb w15, [x10, #0]
	ldrb w9, [x11, #0]
	eor x9, x9, x15
	and x9, x9, x14
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 226b
	lsr x27, x27, #1
	add x28, x28, x28
	sub x22, x22, #1
	cbnz x22, 225b
	ldr x9, [sp, #304]
	sub x9, x25, x9
	sub x9, x9, #1
	add x22, x9, #28
	add x9, x25, #35
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
227:
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
	cbnz x12, 227b
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
228:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
229:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 229b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 228b
	movz x27, #0, lsl #0
230:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
231:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 231b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 230b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #20, lsl #0
232:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 232b
	sub x0, x26, #1
	lsr x0, x0, #63
	b 221f
220:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
233:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 233b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #20, lsl #0
234:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 234b
	add x11, x24, x25
	ldr x12, [sp, #232]
	sub x11, x11, x12
	add x14, x20, #3612
	cbz x12, 235f
237:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 237b
	b 236f
235:
236:
	ldr x9, [sp, #232]
	add x22, x9, #28
	add x9, x22, #8
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
238:
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
	cbnz x12, 238b
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
239:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
240:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 240b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 239b
	movz x27, #0, lsl #0
241:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
242:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 242b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 241b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #20, lsl #0
243:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 243b
	sub x0, x26, #1
	lsr x0, x0, #63
221:
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

vg_rsa_pss_sha1_mgf1_sha1_encode_sha2:
	.arch_extension sha2
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
	add x9, x23, #0
	sub x10, x9, #22
	lsr x10, x10, #63
	cbnz x10, 20f
	ldr x12, [sp, #232]
	sub x9, x9, #22
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
	movz x12, #20, lsl #0
25:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #224]
	add x14, x20, #3612
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
	add x22, x9, #28
	add x9, x22, #8
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
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
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
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
	bl {vg_sha1_compress_sha2}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
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
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
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
	movz x12, #20, lsl #0
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
	movz x28, #0, lsl #0
	movz x9, #0, lsl #0
	add x16, sp, #0
	str x9, [x16, #272]
219:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #8, lsl #0
220:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 220b
	add x11, x24, x25
	add x14, x20, #3584
	movz x12, #20, lsl #0
221:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 221b
	add x10, x20, #3604
	lsr x9, x28, #24
	strb w9, [x10, #0]
	lsr x9, x28, #16
	strb w9, [x10, #1]
	lsr x9, x28, #8
	strb w9, [x10, #2]
	strb w28, [x10, #3]
	movz x22, #24, lsl #0
	movz x9, #1, lsl #0
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3608
	ldrb w9, [x10, #0]
	movz x13, #128, lsl #0
	orr x9, x9, x13
	strb w9, [x10, #0]
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
222:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
223:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 223b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 222b
	movz x27, #0, lsl #0
224:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
225:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 225b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 224b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	ldr x9, [sp, #272]
	add x10, x24, x9
	add x11, x21, #0
	sub x12, x25, x9
	movz x13, #20, lsl #0
	sub x14, x12, x13
	lsr x14, x14, #63
	cbz x14, 226f
	b 227f
226:
	add x12, x13, #0
227:
228:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 228b
	add x28, x28, #1
	ldr x9, [sp, #272]
	add x9, x9, #20
	add x16, sp, #0
	str x9, [x16, #272]
	sub x10, x9, x25
	lsr x10, x10, #63
	cbnz x10, 219b
	ldrb w9, [x24, #0]
	ldr x10, [sp, #248]
	and x9, x9, x10
	strb w9, [x24, #0]
	add x11, x20, #2560
	ldr x14, [sp, #216]
	add x12, x23, #0
229:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 229b
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
	.arch_extension nosha2
	.p2align 6

vg_rsa_pss_sha1_mgf1_sha1_check_encoding_sha2:
	.arch_extension sha2
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
	sub x10, x9, #22
	lsr x10, x10, #63
	cbnz x10, 21f
	ldr x13, [sp, #264]
	cbz x13, 23f
	movz x12, #0, lsl #0
	b 24f
23:
	ldr x12, [sp, #232]
24:
	sub x9, x9, #22
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
	movz x28, #0, lsl #0
	movz x9, #0, lsl #0
	add x16, sp, #0
	str x9, [x16, #272]
27:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #8, lsl #0
28:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 28b
	add x11, x24, x25
	add x14, x20, #3584
	movz x12, #20, lsl #0
29:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 29b
	add x10, x20, #3604
	lsr x9, x28, #24
	strb w9, [x10, #0]
	lsr x9, x28, #16
	strb w9, [x10, #1]
	lsr x9, x28, #8
	strb w9, [x10, #2]
	strb w28, [x10, #3]
	movz x22, #24, lsl #0
	movz x9, #1, lsl #0
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3608
	ldrb w9, [x10, #0]
	movz x13, #128, lsl #0
	orr x9, x9, x13
	strb w9, [x10, #0]
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
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
	bl {vg_sha1_compress_sha2}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
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
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	ldr x9, [sp, #272]
	add x10, x24, x9
	add x11, x21, #0
	sub x12, x25, x9
	movz x13, #20, lsl #0
	sub x14, x12, x13
	lsr x14, x14, #63
	cbz x14, 214f
	b 215f
214:
	add x12, x13, #0
215:
216:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 216b
	add x28, x28, #1
	ldr x9, [sp, #272]
	add x9, x9, #20
	add x16, sp, #0
	str x9, [x16, #272]
	sub x10, x9, x25
	lsr x10, x10, #63
	cbnz x10, 27b
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
217:
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
	cbnz x12, 217b
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
	cbz x9, 218f
	b 219f
218:
	ldr x12, [sp, #232]
	eor x12, x12, x11
	orr x26, x26, x12
219:
	ldr x9, [sp, #264]
	cbz x9, 220f
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
222:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 222b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #20, lsl #0
223:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 223b
	add x11, x24, #0
	add x14, x20, #3612
	add x12, x25, #0
224:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 224b
	ldr x27, [sp, #304]
	add x27, x27, #1
	movz x28, #1, lsl #0
	movz x22, #10, lsl #0
225:
	add x10, x20, #3612
	add x11, x10, x28
	lsr x14, x27, #1
	lsl x14, x14, #1
	sub x14, x27, x14
	movz x9, #0, lsl #0
	sub x14, x9, x14
	add x12, x25, #0
226:
	ldrb w15, [x10, #0]
	ldrb w9, [x11, #0]
	eor x9, x9, x15
	and x9, x9, x14
	eor x15, x15, x9
	strb w15, [x10, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 226b
	lsr x27, x27, #1
	add x28, x28, x28
	sub x22, x22, #1
	cbnz x22, 225b
	ldr x9, [sp, #304]
	sub x9, x25, x9
	sub x9, x9, #1
	add x22, x9, #28
	add x9, x25, #35
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
227:
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
	cbnz x12, 227b
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
228:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
229:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 229b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 228b
	movz x27, #0, lsl #0
230:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
231:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 231b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 230b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #20, lsl #0
232:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 232b
	sub x0, x26, #1
	lsr x0, x0, #63
	b 221f
220:
	add x10, x20, #3584
	movz x9, #0, lsl #0
	movz x12, #256, lsl #0
233:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 233b
	ldr x11, [sp, #208]
	add x14, x20, #3592
	movz x12, #20, lsl #0
234:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 234b
	add x11, x24, x25
	ldr x12, [sp, #232]
	sub x11, x11, x12
	add x14, x20, #3612
	cbz x12, 235f
237:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 237b
	b 236f
235:
236:
	ldr x9, [sp, #232]
	add x22, x9, #28
	add x9, x22, #8
	lsr x9, x9, #6
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha1_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #6
238:
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
	cbnz x12, 238b
	add x19, x20, #2292
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x19, x20, #2048
	add x10, x20, #3640
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #8
	lsr x15, x15, #6
239:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #8, lsl #0
240:
	ldrb w9, [x14, #0]
	and x9, x9, x13
	ldrb w8, [x16, #0]
	orr x8, x8, x9
	strb w8, [x16, #0]
	add x14, x14, #1
	add x16, x16, #1
	sub x17, x17, #1
	cbnz x17, 240b
	add x10, x10, #64
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 239b
	movz x27, #0, lsl #0
241:
	lsl x1, x27, #6
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x15, x22, #8
	lsr x15, x15, #6
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #20, lsl #0
242:
	ldrb w14, [x10, #0]
	ldrb w15, [x11, #0]
	eor x14, x14, x15
	and x14, x14, x13
	eor x15, x15, x14
	strb w15, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 242b
	add x27, x27, #1
	ldr x9, [sp, #280]
	sub x9, x9, x27
	cbnz x9, 241b
	add x19, x20, #2240
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #20, lsl #0
243:
	ldrb w9, [x11, #0]
	ldrb w15, [x10, #0]
	eor x9, x9, x15
	orr x26, x26, x9
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 243b
	sub x0, x26, #1
	lsr x0, x0, #63
221:
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
	.arch_extension nosha2
	.p2align 6

vg_rsa_pss_sha1_mgf1_sha1_sign:
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
	str x2, [x16, #184]
	str x4, [x16, #192]
	str x5, [x16, #200]
	str x6, [x16, #288]
	str x7, [x16, #296]
	add x23, x3, #0
	ldr x9, [sp, #400]
	str x9, [x16, #208]
	ldr x9, [sp, #408]
	str x9, [x16, #224]
	ldr x9, [sp, #416]
	str x9, [x16, #232]
	ldr x20, [sp, #424]
	ldr x9, [sp, #432]
	str x9, [x16, #240]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x2, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x0, x20, #2560
	movz x9, #0, lsl #0
	strb w9, [x0, #0]
	add x0, x0, x26
	add x1, x25, #0
	ldr x2, [sp, #208]
	ldr x3, [sp, #224]
	ldr x4, [sp, #232]
	add x5, x24, #0
	add x6, x20, #3584
	ldr x7, [sp, #240]
	sub x7, x7, #448
	bl {vg_rsa_pss_sha1_mgf1_sha1_encode}
	cbz w0, 22f
	add x16, sp, #0
	ldr x9, [sp, #288]
	str x9, [x16, #0]
	ldr x9, [sp, #296]
	str x9, [x16, #8]
	ldr x9, [sp, #336]
	str x9, [x16, #16]
	ldr x9, [sp, #344]
	str x9, [x16, #24]
	ldr x9, [sp, #352]
	str x9, [x16, #32]
	ldr x9, [sp, #360]
	str x9, [x16, #40]
	ldr x9, [sp, #368]
	str x9, [x16, #48]
	ldr x9, [sp, #376]
	str x9, [x16, #56]
	ldr x9, [sp, #384]
	str x9, [x16, #64]
	ldr x9, [sp, #392]
	str x9, [x16, #72]
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #80]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #88]
	ldr x0, [sp, #216]
	add x1, x23, #0
	ldr x2, [sp, #184]
	add x3, x23, #0
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	add x6, x20, #2560
	add x7, x23, #0
	bl {vg_rsa_private_checked}
	b 23f
22:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
24:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 24b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
25:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 25b
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

vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_sha2:
	.arch_extension sha2
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
	str x2, [x16, #184]
	str x4, [x16, #192]
	str x5, [x16, #200]
	str x6, [x16, #288]
	str x7, [x16, #296]
	add x23, x3, #0
	ldr x9, [sp, #400]
	str x9, [x16, #208]
	ldr x9, [sp, #408]
	str x9, [x16, #224]
	ldr x9, [sp, #416]
	str x9, [x16, #232]
	ldr x20, [sp, #424]
	ldr x9, [sp, #432]
	str x9, [x16, #240]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x2, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x0, x20, #2560
	movz x9, #0, lsl #0
	strb w9, [x0, #0]
	add x0, x0, x26
	add x1, x25, #0
	ldr x2, [sp, #208]
	ldr x3, [sp, #224]
	ldr x4, [sp, #232]
	add x5, x24, #0
	add x6, x20, #3584
	ldr x7, [sp, #240]
	sub x7, x7, #448
	bl {vg_rsa_pss_sha1_mgf1_sha1_encode_sha2}
	cbz w0, 22f
	add x16, sp, #0
	ldr x9, [sp, #288]
	str x9, [x16, #0]
	ldr x9, [sp, #296]
	str x9, [x16, #8]
	ldr x9, [sp, #336]
	str x9, [x16, #16]
	ldr x9, [sp, #344]
	str x9, [x16, #24]
	ldr x9, [sp, #352]
	str x9, [x16, #32]
	ldr x9, [sp, #360]
	str x9, [x16, #40]
	ldr x9, [sp, #368]
	str x9, [x16, #48]
	ldr x9, [sp, #376]
	str x9, [x16, #56]
	ldr x9, [sp, #384]
	str x9, [x16, #64]
	ldr x9, [sp, #392]
	str x9, [x16, #72]
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #80]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #88]
	ldr x0, [sp, #216]
	add x1, x23, #0
	ldr x2, [sp, #184]
	add x3, x23, #0
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	add x6, x20, #2560
	add x7, x23, #0
	bl {vg_rsa_private_checked}
	b 23f
22:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
24:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 24b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
25:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 25b
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
	.arch_extension nosha2
	.p2align 6

vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed:
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
	str x0, [x16, #184]
	str x2, [x16, #192]
	str x3, [x16, #200]
	str x4, [x16, #208]
	str x5, [x16, #216]
	str x7, [x16, #232]
	add x23, x1, #0
	ldr x9, [sp, #336]
	add w9, w9, #0
	str x9, [x16, #264]
	ldr x20, [sp, #344]
	ldr x9, [sp, #352]
	str x9, [x16, #240]
	ldr x9, [sp, #360]
	str x9, [x16, #312]
	ldr x9, [sp, #368]
	str x9, [x16, #320]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x0, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x16, sp, #0
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #0]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #8]
	add x0, x20, #0
	add x1, x23, #0
	ldr x2, [sp, #312]
	ldr x3, [sp, #320]
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	ldr x6, [sp, #216]
	add x7, x23, #0
	bl {vg_rsa_public_precomputed_checked}
	add x1, x20, x26
	ldrb w9, [x20, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x26
	and x9, x9, x10
	sub x26, x9, #1
	lsr x26, x26, #63
	ldr x0, [sp, #208]
	add x2, x25, #0
	add x3, x24, #0
	ldr x4, [sp, #232]
	ldr x5, [sp, #264]
	add x9, x23, #7
	lsr x9, x9, #3
	ldr x7, [sp, #240]
	sub x7, x7, x9
	lsl x9, x9, #3
	add x6, x20, x9
	bl {vg_rsa_pss_sha1_mgf1_sha1_check_encoding}
	and x0, x0, x26
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

vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_sha2:
	.arch_extension sha2
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
	str x0, [x16, #184]
	str x2, [x16, #192]
	str x3, [x16, #200]
	str x4, [x16, #208]
	str x5, [x16, #216]
	str x7, [x16, #232]
	add x23, x1, #0
	ldr x9, [sp, #336]
	add w9, w9, #0
	str x9, [x16, #264]
	ldr x20, [sp, #344]
	ldr x9, [sp, #352]
	str x9, [x16, #240]
	ldr x9, [sp, #360]
	str x9, [x16, #312]
	ldr x9, [sp, #368]
	str x9, [x16, #320]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x0, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x16, sp, #0
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #0]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #8]
	add x0, x20, #0
	add x1, x23, #0
	ldr x2, [sp, #312]
	ldr x3, [sp, #320]
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	ldr x6, [sp, #216]
	add x7, x23, #0
	bl {vg_rsa_public_precomputed_checked}
	add x1, x20, x26
	ldrb w9, [x20, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x26
	and x9, x9, x10
	sub x26, x9, #1
	lsr x26, x26, #63
	ldr x0, [sp, #208]
	add x2, x25, #0
	add x3, x24, #0
	ldr x4, [sp, #232]
	ldr x5, [sp, #264]
	add x9, x23, #7
	lsr x9, x9, #3
	ldr x7, [sp, #240]
	sub x7, x7, x9
	lsl x9, x9, #3
	add x6, x20, x9
	bl {vg_rsa_pss_sha1_mgf1_sha1_check_encoding_sha2}
	and x0, x0, x26
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
	.arch_extension nosha2
	.p2align 6
