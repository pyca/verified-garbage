// The functions of `src/aes_ccm.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ccm_seal_aes:
	sub sp, sp, #416
	add x16, sp, #0
	ldr x17, [sp, #416]
	str x17, [x16, #0]
	ldr x17, [sp, #424]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 21f
	add x9, x9, #64
	b 22f
21:
22:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	cbz x24, 23f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 25f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 26f
25:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 27f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 28f
27:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
28:
26:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 29f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 211f
	add x10, x9, #0
	b 212f
211:
	add x10, x24, #0
212:
	b 210f
29:
	add x10, x9, #0
210:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_aes}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 214f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	b 215f
214:
215:
	b 24f
23:
24:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_aes}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 217f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
219:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 219b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	b 218f
217:
218:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #0
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_aes}
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 220f
222:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 223f
	add x26, x24, #0
	b 224f
223:
	add x26, x10, #0
224:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32_aes}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 222b
	b 221f
220:
221:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 225f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_aes}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	ldr x11, [x19, #240]
	add x12, x19, #0
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #416
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #416
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	add sp, sp, #416
	ret
	.p2align 6

vg_aes_ccm_open_aes:
	sub sp, sp, #416
	add x16, sp, #0
	ldr x17, [sp, #416]
	str x17, [x16, #0]
	ldr x17, [sp, #424]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 21f
23:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 24f
	add x26, x24, #0
	b 25f
24:
	add x26, x10, #0
25:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32_aes}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 23b
	b 22f
21:
22:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 26f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_aes}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
28:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 28b
	b 27f
26:
27:
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 29f
	add x9, x9, #64
	b 210f
29:
210:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	cbz x24, 211f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 213f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 214f
213:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 215f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 216f
215:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
216:
214:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 217f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 219f
	add x10, x9, #0
	b 220f
219:
	add x10, x24, #0
220:
	b 218f
217:
	add x10, x9, #0
218:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_aes}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 222f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
224:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 224b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	b 223f
222:
223:
	b 212f
211:
212:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_aes}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 225f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_aes}
	b 226f
225:
226:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #96
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_aes}
	ldr x12, [x19, #240]
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	add x11, x19, #256
	add x12, x19, #96
	add x13, x20, #0
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x0, #1, lsl #0
	sub x0, x0, x10
	sub x11, x10, #1
	add x12, x27, #0
	dup v16.16b, w11
	lsr x14, x28, #4
	lsl x13, x14, #4
	sub x13, x28, x13
	cbz x14, 230f
232:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 232b
	b 231f
230:
231:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #416
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #416
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	add sp, sp, #416
	ret
	.p2align 6

vg_aes_ccm_seal_neon:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 21f
	add x9, x9, #64
	b 22f
21:
22:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	cbz x24, 23f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 25f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 26f
25:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 27f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 28f
27:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
28:
26:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 29f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 211f
	add x10, x9, #0
	b 212f
211:
	add x10, x24, #0
212:
	b 210f
29:
	add x10, x9, #0
210:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_neon}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 214f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	b 215f
214:
215:
	b 24f
23:
24:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_neon}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 217f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
219:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 219b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	b 218f
217:
218:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #0
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_neon}
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 220f
222:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 223f
	add x26, x24, #0
	b 224f
223:
	add x26, x10, #0
224:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32_neon}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 222b
	b 221f
220:
221:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 225f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_neon}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	ldr x11, [x19, #240]
	add x12, x19, #0
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #2592
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	add sp, sp, #2592
	ret
	.p2align 6

vg_aes_ccm_open_neon:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 21f
23:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 24f
	add x26, x24, #0
	b 25f
24:
	add x26, x10, #0
25:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32_neon}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 23b
	b 22f
21:
22:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 26f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_neon}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
28:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 28b
	b 27f
26:
27:
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 29f
	add x9, x9, #64
	b 210f
29:
210:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	cbz x24, 211f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 213f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 214f
213:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 215f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 216f
215:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
216:
214:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 217f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 219f
	add x10, x9, #0
	b 220f
219:
	add x10, x24, #0
220:
	b 218f
217:
	add x10, x9, #0
218:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_neon}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 222f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
224:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 224b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	b 223f
222:
223:
	b 212f
211:
212:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update_neon}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 225f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update_neon}
	b 226f
225:
226:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #96
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_neon}
	ldr x12, [x19, #240]
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	add x11, x19, #256
	add x12, x19, #96
	add x13, x20, #0
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x0, #1, lsl #0
	sub x0, x0, x10
	sub x11, x10, #1
	add x12, x27, #0
	dup v16.16b, w11
	lsr x14, x28, #4
	lsl x13, x14, #4
	sub x13, x28, x13
	cbz x14, 230f
232:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 232b
	b 231f
230:
231:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2592
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	add sp, sp, #2592
	ret
	.p2align 6

vg_aes_ccm_seal:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 21f
	add x9, x9, #64
	b 22f
21:
22:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	cbz x24, 23f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 25f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 26f
25:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 27f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 28f
27:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
28:
26:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 29f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 211f
	add x10, x9, #0
	b 212f
211:
	add x10, x24, #0
212:
	b 210f
29:
	add x10, x9, #0
210:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 214f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	b 215f
214:
215:
	b 24f
23:
24:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 217f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
219:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 219b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #0
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	b 218f
217:
218:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #0
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32}
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 220f
222:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 223f
	add x26, x24, #0
	b 224f
223:
	add x26, x10, #0
224:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 222b
	b 221f
220:
221:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 225f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	ldr x11, [x19, #240]
	add x12, x19, #0
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #2592
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	add sp, sp, #2592
	ret
	.p2align 6

vg_aes_ccm_open:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	ldr x10, [sp, #8]
	ldr x11, [sp, #0]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x10, #0
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x3, [x19, #232]
	str x11, [x19, #240]
	add x27, x6, #0
	add x28, x7, #0
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #14, lsl #0
	sub x9, x9, x3
	strb w9, [x19, #48]
	add x11, x19, #49
	add x12, x2, #0
	add x13, x3, #0
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	add x23, x27, #0
	lsr x24, x28, #4
	movz x25, #1, lsl #0
	cbz x24, 21f
23:
	add w9, w25, #0
	movz x10, #1, lsl #32
	sub x10, x10, x9
	sub x11, x24, x10
	lsr x11, x11, #63
	cbz x11, 24f
	add x26, x24, #0
	b 25f
24:
	add x26, x10, #0
25:
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x23, #0
	add x4, x26, #0
	bl {vg_aes_ctr32}
	sub x24, x24, x26
	add x25, x25, x26
	lsl x9, x26, #4
	add x23, x23, x9
	cbnz x24, 23b
	b 22f
21:
22:
	movz x9, #15, lsl #0
	and x26, x28, x9
	cbz x26, 26f
	add x9, x25, #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #80
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32}
	add x11, x19, #80
	add x12, x23, #0
	add x13, x26, #0
28:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 28b
	b 27f
26:
27:
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	sub x9, x20, #2
	lsl x9, x9, #2
	ldr x10, [x19, #232]
	movz x11, #14, lsl #0
	sub x11, x11, x10
	add x9, x9, x11
	cbz x24, 29f
	add x9, x9, #64
	b 210f
29:
210:
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #32]
	strb w9, [x19, #32]
	rev x12, x28
	orr x11, x11, x12
	str x11, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	cbz x24, 211f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x9, x24, #32
	cbz x9, 213f
	movz x9, #65535, lsl #0
	str x9, [x19, #32]
	rev x9, x24
	add x10, x19, #34
	str x9, [x10, #0]
	movz x25, #10, lsl #0
	b 214f
213:
	lsr x9, x24, #8
	sub x9, x9, #255
	lsr x9, x9, #63
	cbz x9, 215f
	rev x9, x24
	lsr x9, x9, #48
	str x9, [x19, #32]
	movz x25, #2, lsl #0
	b 216f
215:
	rev x9, x24
	lsr x9, x9, #16
	movz x10, #65279, lsl #0
	orr x9, x9, x10
	str x9, [x19, #32]
	movz x25, #6, lsl #0
216:
214:
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 217f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 219f
	add x10, x9, #0
	b 220f
219:
	add x10, x24, #0
220:
	b 218f
217:
	add x10, x9, #0
218:
	add x11, x19, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	add x23, x23, x10
	sub x24, x24, x10
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 222f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
224:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 224b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	b 223f
222:
223:
	b 212f
211:
212:
	add x23, x27, #0
	add x24, x28, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x23, #0
	lsr x4, x24, #4
	bl {vg_cmac_aes_update}
	movz x9, #15, lsl #0
	and x13, x24, x9
	cbz x13, 225f
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	lsr x10, x24, #4
	lsl x10, x10, #4
	add x12, x23, x10
	add x11, x19, #32
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x5, x19, #384
	add x3, x19, #32
	movz x4, #1, lsl #0
	bl {vg_cmac_aes_update}
	b 226f
225:
226:
	movz x9, #0, lsl #0
	ldr x10, [x19, #48]
	ldr x11, [x19, #56]
	str x10, [x19, #64]
	rev x9, x9
	orr x11, x11, x9
	str x11, [x19, #72]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #64
	add x5, x19, #384
	add x3, x19, #96
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32}
	ldr x12, [x19, #240]
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x13, x20, #0
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	add x11, x19, #256
	add x12, x19, #96
	add x13, x20, #0
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x0, #1, lsl #0
	sub x0, x0, x10
	sub x11, x10, #1
	add x12, x27, #0
	dup v16.16b, w11
	lsr x14, x28, #4
	lsl x13, x14, #4
	sub x13, x28, x13
	cbz x14, 230f
232:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 232b
	b 231f
230:
231:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
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
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2592
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	add sp, sp, #2592
	ret
	.p2align 6
