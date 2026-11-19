// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init_aes:
	sub sp, sp, #1024
	add x3, sp, #0
	str x20, [x3, #168]
	str x21, [x3, #176]
	str x22, [x3, #184]
	str x23, [x3, #192]
	str x24, [x3, #200]
	str x25, [x3, #208]
	str x26, [x3, #216]
	str x27, [x3, #224]
	str x28, [x3, #232]
	str x30, [x3, #240]
	str x19, [x3, #160]
	add x19, x3, #0
	add x20, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch_aes}
	movz x9, #0, lsl #0
	str x9, [x20, #240]
	str x9, [x20, #248]
	add x2, x20, #240
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #1024
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
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1024
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
	add sp, sp, #1024
	ret
	.p2align 6

vg_aes_ocb_seal_aes:
	sub sp, sp, #544
	add x16, sp, #0
	ldr x17, [sp, #544]
	str x17, [x16, #0]
	ldr x17, [sp, #552]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x11, [sp, #0]
	add x12, x19, #0
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #544
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
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
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #544
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
	add sp, sp, #544
	ret
	.p2align 6

vg_aes_ocb_open_aes:
	sub sp, sp, #544
	add x16, sp, #0
	ldr x17, [sp, #544]
	str x17, [x16, #0]
	ldr x17, [sp, #552]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_decrypt_blocks_aes}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #128]
	str x10, [x19, #136]
	ldr x9, [x19, #128]
	ldr x10, [x19, #136]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #128]
	str x10, [x19, #136]
	add x11, x19, #0
	ldr x12, [sp, #0]
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	movz x13, #0, lsl #0
	add x11, x19, #0
	add x12, x19, #128
	ldr x24, [x19, #248]
249:
	ldrb w9, [x11, #0]
	ldrb w10, [x12, #0]
	eor x9, x9, x10
	orr x13, x13, x9
	add x11, x11, #1
	add x12, x12, #1
	sub x24, x24, #1
	cbnz x24, 249b
	sub x13, x13, #1
	lsr x13, x13, #63
	str x13, [x19, #0]
	add x23, x21, #0
	add x24, x28, #0
	ldr x9, [x19, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x9
	cbz x24, 250f
252:
	lsr x9, x24, #6
	cbz x9, 253f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 254f
253:
	lsr x9, x24, #4
	cbz x9, 255f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 256f
255:
	ldrb w9, [x23, #0]
	and w9, w9, w10
	strb w9, [x23, #0]
	add x23, x23, #1
	sub x24, x24, #1
256:
254:
	cbnz x24, 252b
	b 251f
250:
251:
	ldr x0, [x19, #0]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #544
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
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
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #544
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
	add sp, sp, #544
	ret
	.p2align 6

vg_aes_ocb_init_neon:
	sub sp, sp, #2560
	add x3, sp, #0
	str x20, [x3, #168]
	str x21, [x3, #176]
	str x22, [x3, #184]
	str x23, [x3, #192]
	str x24, [x3, #200]
	str x25, [x3, #208]
	str x26, [x3, #216]
	str x27, [x3, #224]
	str x28, [x3, #232]
	str x30, [x3, #240]
	str x19, [x3, #160]
	add x19, x3, #0
	add x20, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch}
	movz x9, #0, lsl #0
	str x9, [x20, #240]
	str x9, [x20, #248]
	add x2, x20, #240
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2560
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
	sub sp, sp, #2560
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
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_ocb_seal_neon:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x11, [sp, #0]
	add x12, x19, #0
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
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

vg_aes_ocb_open_neon:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_decrypt_blocks_neon}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #128]
	str x10, [x19, #136]
	ldr x9, [x19, #128]
	ldr x10, [x19, #136]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #128]
	str x10, [x19, #136]
	add x11, x19, #0
	ldr x12, [sp, #0]
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	movz x13, #0, lsl #0
	add x11, x19, #0
	add x12, x19, #128
	ldr x24, [x19, #248]
249:
	ldrb w9, [x11, #0]
	ldrb w10, [x12, #0]
	eor x9, x9, x10
	orr x13, x13, x9
	add x11, x11, #1
	add x12, x12, #1
	sub x24, x24, #1
	cbnz x24, 249b
	sub x13, x13, #1
	lsr x13, x13, #63
	str x13, [x19, #0]
	add x23, x21, #0
	add x24, x28, #0
	ldr x9, [x19, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x9
	cbz x24, 250f
252:
	lsr x9, x24, #6
	cbz x9, 253f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 254f
253:
	lsr x9, x24, #4
	cbz x9, 255f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 256f
255:
	ldrb w9, [x23, #0]
	and w9, w9, w10
	strb w9, [x23, #0]
	add x23, x23, #1
	sub x24, x24, #1
256:
254:
	cbnz x24, 252b
	b 251f
250:
251:
	ldr x0, [x19, #0]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
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

vg_aes_ocb_init:
	sub sp, sp, #2560
	add x3, sp, #0
	str x20, [x3, #168]
	str x21, [x3, #176]
	str x22, [x3, #184]
	str x23, [x3, #192]
	str x24, [x3, #200]
	str x25, [x3, #208]
	str x26, [x3, #216]
	str x27, [x3, #224]
	str x28, [x3, #232]
	str x30, [x3, #240]
	str x19, [x3, #160]
	add x19, x3, #0
	add x20, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch}
	movz x9, #0, lsl #0
	str x9, [x20, #240]
	str x9, [x20, #248]
	add x2, x20, #240
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2560
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
	sub sp, sp, #2560
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
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_ocb_seal:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v5.16b, v5.16b, v4.16b
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x11, [sp, #0]
	add x12, x19, #0
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
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

vg_aes_ocb_open:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #168]
	str x21, [x9, #176]
	str x22, [x9, #184]
	str x23, [x9, #192]
	str x24, [x9, #200]
	str x25, [x9, #208]
	str x26, [x9, #216]
	str x27, [x9, #224]
	str x28, [x9, #232]
	str x30, [x9, #240]
	str x19, [x9, #160]
	add x19, x9, #0
	add x20, x0, #0
	add x21, x6, #0
	add x22, x1, #0
	add x28, x7, #0
	str x2, [x19, #272]
	str x3, [x19, #280]
	str x4, [x19, #256]
	str x5, [x19, #264]
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	ldr x9, [x20, #240]
	rev x9, x9
	ldr x10, [x20, #248]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #64]
	rev x10, x10
	str x10, [x19, #72]
	ldr x9, [x19, #64]
	rev x9, x9
	ldr x10, [x19, #72]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #80]
	rev x10, x10
	str x10, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	ldr x12, [x19, #272]
	ldr x13, [x19, #280]
	add x11, x19, #128
	sub x11, x11, x13
	sub x14, x11, #1
	movz x9, #1, lsl #0
	strb w9, [x14, #0]
20:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 20b
	ldr x10, [x19, #248]
	movz x11, #15, lsl #0
	and x10, x10, x11
	lsl x10, x10, #4
	ldrb w9, [x19, #112]
	orr x9, x9, x10
	strb w9, [x19, #112]
	ldrb w9, [x19, #127]
	movz x11, #63, lsl #0
	and x10, x9, x11
	str x10, [x19, #288]
	movz x11, #192, lsl #0
	and x9, x9, x11
	strb w9, [x19, #127]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #112]
	rev x9, x9
	ldr x10, [x19, #120]
	rev x10, x10
	lsl x11, x9, #8
	lsr x13, x10, #56
	orr x11, x11, x13
	eor x11, x11, x9
	ldr x12, [x19, #288]
	lsr x13, x12, #0
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #1
	lsr x15, x10, #63
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #1
	lsr x15, x11, #63
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #1
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #1
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #2
	lsr x15, x10, #62
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #2
	lsr x15, x11, #62
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #2
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #2
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #4
	lsr x15, x10, #60
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #4
	lsr x15, x11, #60
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #4
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #3
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #8
	lsr x15, x10, #56
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #8
	lsr x15, x11, #56
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #8
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #4
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #16
	lsr x15, x10, #48
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #16
	lsr x15, x11, #48
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #16
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	lsr x13, x12, #5
	movz x14, #1, lsl #0
	and x13, x13, x14
	movz x14, #0, lsl #0
	sub x13, x14, x13
	lsl x14, x9, #32
	lsr x15, x10, #32
	orr x14, x14, x15
	eor x14, x14, x9
	and x14, x14, x13
	eor x9, x9, x14
	lsl x14, x10, #32
	lsr x15, x11, #32
	orr x14, x14, x15
	eor x14, x14, x10
	and x14, x14, x13
	eor x10, x10, x14
	lsl x14, x11, #32
	eor x14, x14, x11
	and x14, x14, x13
	eor x11, x11, x14
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	str x9, [x19, #304]
	str x10, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #48]
	str x9, [x19, #56]
	movz x9, #0, lsl #0
	str x9, [x19, #144]
	str x9, [x19, #152]
	ldr x23, [x19, #256]
	ldr x26, [x19, #264]
	lsr x26, x26, #4
	movz x25, #1, lsl #0
	cbz x26, 21f
23:
	sub x9, x26, #8
	lsr x9, x9, #63
	add x24, x26, #0
	cbz x9, 24f
	b 25f
24:
	movz x24, #8, lsl #0
25:
	add x27, x19, #384
	add x15, x24, #0
26:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 27f
	b 28f
27:
29:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 29b
28:
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x27, #0]
	str x10, [x27, #8]
	add x27, x27, #16
	add x23, x23, #16
	add x25, x25, #1
	sub x15, x15, #1
	cbnz x15, 26b
	add x2, x19, #384
	add x3, x24, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	add x27, x19, #384
	add x15, x24, #0
210:
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x27, #0]
	ldr x12, [x27, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	add x27, x27, #16
	sub x15, x15, #1
	cbnz x15, 210b
	sub x26, x26, x24
	cbnz x26, 23b
	b 22f
21:
22:
	ldr x24, [x19, #264]
	movz x10, #15, lsl #0
	and x24, x24, x10
	cbz x24, 211f
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #144]
	str x10, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #384]
	str x9, [x19, #392]
	add x11, x19, #384
	add x12, x23, #0
	add x13, x24, #0
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #384]
	ldr x10, [x19, #392]
	ldr x11, [x19, #144]
	ldr x12, [x19, #152]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #384]
	str x10, [x19, #392]
	add x2, x19, #384
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #48]
	ldr x10, [x19, #56]
	ldr x11, [x19, #384]
	ldr x12, [x19, #392]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #48]
	str x10, [x19, #56]
	b 212f
211:
212:
	lsr x26, x28, #4
	cbz x26, 214f
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 216f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
218:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
219:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 219b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 218b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 220f
222:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 223f
	b 224f
223:
225:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 225b
224:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 222b
	b 221f
220:
221:
	b 217f
216:
226:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 227f
	b 228f
227:
229:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 229b
228:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 226b
217:
	add x2, x21, #0
	add x3, x26, #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_decrypt_blocks}
	ldr x9, [x19, #304]
	ldr x10, [x19, #312]
	str x9, [x19, #16]
	str x10, [x19, #24]
	add x23, x21, #0
	add x24, x26, #0
	movz x25, #1, lsl #0
	lsr x9, x24, #3
	cbz x9, 230f
	ldr q0, [x19, #80]
	ldr x9, [x19, #80]
	rev x9, x9
	ldr x10, [x19, #88]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q1, [x19, #96]
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	ldr q2, [x19, #96]
	ldr q3, [x19, #16]
	ldr q5, [x19, #32]
232:
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v2.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v1.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	eor v3.16b, v3.16b, v0.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	umov x9, v2.d[0]
	umov x10, v2.d[1]
	str x9, [x19, #96]
	str x10, [x19, #104]
	lsr x14, x25, #2
233:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 233b
	ldr q6, [x19, #96]
	eor v3.16b, v3.16b, v6.16b
	ldr q4, [x23, #0]
	eor v4.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v4.16b
	str q4, [x23, #0]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	lsr x9, x24, #3
	cbnz x9, 232b
	str q3, [x19, #16]
	str q5, [x19, #32]
	cbz x24, 234f
236:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 237f
	b 238f
237:
239:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 239b
238:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 236b
	b 235f
234:
235:
	b 231f
230:
240:
	ldr x9, [x19, #80]
	ldr x10, [x19, #88]
	str x9, [x19, #96]
	str x10, [x19, #104]
	add x14, x25, #0
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 241f
	b 242f
241:
243:
	ldr x9, [x19, #96]
	rev x9, x9
	ldr x10, [x19, #104]
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x12, x12, x11
	movz x13, #135, lsl #0
	and x12, x12, x13
	lsr x11, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x11
	lsl x10, x10, #1
	eor x10, x10, x12
	rev x9, x9
	str x9, [x19, #96]
	rev x10, x10
	str x10, [x19, #104]
	lsr x14, x14, #1
	movz x12, #1, lsl #0
	and x12, x14, x12
	cbz x12, 243b
242:
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x23, #0]
	ldr x10, [x23, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x23, #0]
	str x10, [x23, #8]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x23, #0]
	ldr x12, [x23, #8]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	add x23, x23, #16
	add x25, x25, #1
	sub x24, x24, #1
	cbnz x24, 240b
231:
	b 215f
214:
215:
	movz x10, #15, lsl #0
	and x24, x28, x10
	sub x9, x28, x24
	add x23, x21, x9
	cbz x24, 244f
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	ldr x11, [x20, #240]
	ldr x12, [x20, #248]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	add x11, x19, #112
	add x12, x23, #0
	add x13, x24, #0
246:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	add x11, x19, #128
	add x12, x23, #0
	add x13, x24, #0
247:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 247b
	movz x9, #128, lsl #0
	strb w9, [x11, #0]
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	ldr x11, [x19, #128]
	ldr x12, [x19, #136]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #32]
	str x10, [x19, #40]
	b 245f
244:
245:
	ldr x9, [x19, #32]
	ldr x10, [x19, #40]
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	ldr x11, [x19, #64]
	ldr x12, [x19, #72]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #112]
	str x10, [x19, #120]
	add x2, x19, #112
	movz x3, #1, lsl #0
	add x0, x20, #0
	add x1, x22, #0
	add x4, x19, #512
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x19, #112]
	ldr x10, [x19, #120]
	str x9, [x19, #128]
	str x10, [x19, #136]
	ldr x9, [x19, #128]
	ldr x10, [x19, #136]
	ldr x11, [x19, #48]
	ldr x12, [x19, #56]
	eor x9, x9, x11
	eor x10, x10, x12
	str x9, [x19, #128]
	str x10, [x19, #136]
	add x11, x19, #0
	ldr x12, [sp, #0]
	ldr x13, [x19, #248]
248:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 248b
	movz x13, #0, lsl #0
	add x11, x19, #0
	add x12, x19, #128
	ldr x24, [x19, #248]
249:
	ldrb w9, [x11, #0]
	ldrb w10, [x12, #0]
	eor x9, x9, x10
	orr x13, x13, x9
	add x11, x11, #1
	add x12, x12, #1
	sub x24, x24, #1
	cbnz x24, 249b
	sub x13, x13, #1
	lsr x13, x13, #63
	str x13, [x19, #0]
	add x23, x21, #0
	add x24, x28, #0
	ldr x9, [x19, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x9
	cbz x24, 250f
252:
	lsr x9, x24, #6
	cbz x9, 253f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 254f
253:
	lsr x9, x24, #4
	cbz x9, 255f
	dup v0.2d, x10
	ldr q1, [x23, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x23, #0]
	add x23, x23, #16
	sub x24, x24, #16
	b 256f
255:
	ldrb w9, [x23, #0]
	and w9, w9, w10
	strb w9, [x23, #0]
	add x23, x23, #1
	sub x24, x24, #1
256:
254:
	cbnz x24, 252b
	b 251f
250:
251:
	ldr x0, [x19, #0]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2592
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
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
