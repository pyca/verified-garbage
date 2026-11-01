// The functions of `src/aes_siv.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x3, sp, #0
	str x19, [x3, #2176]
	str x20, [x3, #2184]
	str x21, [x3, #2192]
	str x22, [x3, #2200]
	str x30, [x3, #2208]
	add x19, x0, #0
	lsr x20, x1, #1
	add x21, x2, #0
	add x22, x3, #0
	add x1, x20, #0
	bl {vg_aes_expand_key_scratch_aes}
	add x0, x21, #0
	lsr x1, x20, #2
	add x1, x1, #6
	add x2, x21, #240
	add x3, x22, #0
	bl {vg_cmac_aes_subkeys_aes}
	add x0, x19, x20
	add x1, x20, #0
	add x2, x21, #272
	add x3, x22, #0
	bl {vg_aes_expand_key_scratch_aes}
	ldr x19, [x22, #2176]
	ldr x20, [x22, #2184]
	ldr x21, [x22, #2192]
	ldr x30, [x22, #2208]
	ldr x22, [x22, #2200]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_siv_init:
	sub sp, sp, #2560
	add x3, sp, #0
	str x19, [x3, #2176]
	str x20, [x3, #2184]
	str x21, [x3, #2192]
	str x22, [x3, #2200]
	str x30, [x3, #2208]
	add x19, x0, #0
	lsr x20, x1, #1
	add x21, x2, #0
	add x22, x3, #0
	add x1, x20, #0
	bl {vg_aes_expand_key_scratch}
	add x0, x21, #0
	lsr x1, x20, #2
	add x1, x1, #6
	add x2, x21, #240
	add x3, x22, #0
	bl {vg_cmac_aes_subkeys}
	add x0, x19, x20
	add x1, x20, #0
	add x2, x21, #272
	add x3, x22, #0
	bl {vg_aes_expand_key_scratch}
	ldr x19, [x22, #2176]
	ldr x20, [x22, #2184]
	ldr x21, [x22, #2192]
	ldr x30, [x22, #2208]
	ldr x22, [x22, #2200]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_siv_encrypt_aes:
	.arch_extension aes
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #2576
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_siv_decrypt_aes:
	.arch_extension aes
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
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
	add sp, sp, #2576
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_siv_encrypt_aes_cbc:
	.arch_extension aes
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #2576
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_siv_decrypt_aes_cbc:
	.arch_extension aes
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update_aes_cbc}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize_aes}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
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
	add sp, sp, #2576
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_siv_encrypt:
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #2576
	ret
	.p2align 6

vg_aes_siv_decrypt:
	sub sp, sp, #2576
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #2560]
	str x9, [x19, #2568]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #2560
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	ldr x9, [x19, #2560]
	ldr x10, [x19, #2568]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #2560]
	str x10, [x19, #2568]
	ldr x9, [x19, #2560]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #2560]
	ldr x9, [x19, #2568]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #2568]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #256
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #2560]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #2568]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #256
	bl {vg_cmac_aes_update}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #2560]
	str x9, [x19, #144]
	ldr x9, [x19, #2568]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #256
	bl {vg_cmac_aes_finalize}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
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
	add sp, sp, #2576
	ret
	.p2align 6
