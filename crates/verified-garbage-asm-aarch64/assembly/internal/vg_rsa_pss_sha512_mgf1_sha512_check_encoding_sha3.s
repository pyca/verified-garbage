// The functions of `src/internal/vg_rsa_pss_sha512_mgf1_sha512_check_encoding_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha512_mgf1_sha512_check_encoding_sha3:
	.arch_extension sha3
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
	sub x10, x9, #66
	lsr x10, x10, #63
	cbnz x10, 21f
	ldr x13, [sp, #264]
	cbz x13, 23f
	movz x12, #0, lsl #0
	b 24f
23:
	ldr x12, [sp, #232]
24:
	sub x9, x9, #66
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
	movz x12, #16, lsl #0
28:
	str x9, [x10, #0]
	add x10, x10, #8
	sub x12, x12, #1
	cbnz x12, 28b
	add x11, x24, x25
	add x14, x20, #3584
	movz x12, #64, lsl #0
29:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 29b
	add x10, x20, #3648
	lsr x9, x28, #24
	strb w9, [x10, #0]
	lsr x9, x28, #16
	strb w9, [x10, #1]
	lsr x9, x28, #8
	strb w9, [x10, #2]
	strb w28, [x10, #3]
	movz x22, #68, lsl #0
	movz x9, #1, lsl #0
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha512_init}
	add x10, x20, #3652
	ldrb w9, [x10, #0]
	movz x13, #128, lsl #0
	orr x9, x9, x13
	strb w9, [x10, #0]
	add x19, x20, #2192
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x19, x20, #2048
	add x10, x20, #3696
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #16
	lsr x15, x15, #7
210:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #16, lsl #0
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
	add x10, x10, #128
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 210b
	movz x27, #0, lsl #0
212:
	lsl x1, x27, #7
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	add x15, x22, #16
	lsr x15, x15, #7
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #64, lsl #0
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
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	add x19, x20, #2048
	ldr x9, [sp, #272]
	add x10, x24, x9
	add x11, x21, #0
	sub x12, x25, x9
	movz x13, #64, lsl #0
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
	add x9, x9, #64
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
	movz x12, #64, lsl #0
223:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 223b
	add x11, x24, #0
	add x14, x20, #3656
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
	add x10, x20, #3656
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
	add x22, x9, #72
	add x9, x25, #87
	lsr x9, x9, #7
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha512_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #7
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
	add x19, x20, #2192
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x19, x20, #2048
	add x10, x20, #3696
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #16
	lsr x15, x15, #7
228:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #16, lsl #0
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
	add x10, x10, #128
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 228b
	movz x27, #0, lsl #0
230:
	lsl x1, x27, #7
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	add x15, x22, #16
	lsr x15, x15, #7
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #64, lsl #0
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
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #64, lsl #0
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
	movz x12, #64, lsl #0
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
	add x14, x20, #3656
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
	add x22, x9, #72
	add x9, x22, #16
	lsr x9, x9, #7
	add x9, x9, #1
	add x16, sp, #0
	str x9, [x16, #280]
	add x0, x19, #0
	bl {vg_sha512_init}
	add x10, x20, #3584
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	lsl x12, x12, #7
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
	add x19, x20, #2192
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x19, x20, #2048
	add x10, x20, #3696
	movz x11, #0, lsl #0
	ldr x12, [sp, #280]
	add x15, x22, #16
	lsr x15, x15, #7
239:
	eor x13, x11, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x14, x20, #2368
	add x16, x10, #0
	movz x17, #16, lsl #0
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
	add x10, x10, #128
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 239b
	movz x27, #0, lsl #0
241:
	lsl x1, x27, #7
	add x1, x1, x20
	add x1, x1, #3584
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	add x15, x22, #16
	lsr x15, x15, #7
	eor x13, x27, x15
	sub x13, x13, #1
	lsr x13, x13, #63
	movz x9, #0, lsl #0
	sub x13, x9, x13
	add x10, x20, #2048
	add x11, x20, #2240
	movz x12, #64, lsl #0
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
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	add x19, x20, #2048
	add x11, x21, #0
	add x10, x24, x25
	movz x12, #64, lsl #0
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
	.arch_extension nosha3
	.p2align 6
