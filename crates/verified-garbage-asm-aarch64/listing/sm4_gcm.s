// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
	sub sp, sp, #3264
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #3168]
	str x20, [x5, #3176]
	str x21, [x5, #3184]
	str x22, [x5, #3192]
	str x23, [x5, #3200]
	str x24, [x5, #3208]
	str x25, [x5, #3216]
	str x26, [x5, #3224]
	str x27, [x5, #3232]
	str x28, [x5, #3240]
	ldr x6, [x1, #0]
	rev x6, x6
	ldr x7, [x1, #8]
	rev x7, x7
	str x6, [x5, #3248]
	str x7, [x5, #3256]
	add w10, w7, w3
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x10
	rev x6, x6
	rev x7, x7
	str x7, [x1, #8]
	str x6, [x1, #0]
	add x23, x2, #0
	add x24, x3, #0
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	movz x1, #0, lsl #0
	add x2, x5, #0
	movz x3, #396, lsl #0
	bl {vg_sm4_prepare_keys}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	cbz x24, 20f
22:
	ldr x6, [x5, #3248]
	ldr x7, [x5, #3256]
	movz x9, #1, lsl #0
	rev x8, x6
	str x8, [x5, #768]
	rev x8, x7
	str x8, [x5, #776]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #784]
	rev x8, x7
	str x8, [x5, #792]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #800]
	rev x8, x7
	str x8, [x5, #808]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #816]
	rev x8, x7
	str x8, [x5, #824]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #832]
	rev x8, x7
	str x8, [x5, #840]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #848]
	rev x8, x7
	str x8, [x5, #856]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #864]
	rev x8, x7
	str x8, [x5, #872]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #880]
	rev x8, x7
	str x8, [x5, #888]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #896]
	rev x8, x7
	str x8, [x5, #904]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #912]
	rev x8, x7
	str x8, [x5, #920]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #928]
	rev x8, x7
	str x8, [x5, #936]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #944]
	rev x8, x7
	str x8, [x5, #952]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #960]
	rev x8, x7
	str x8, [x5, #968]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #976]
	rev x8, x7
	str x8, [x5, #984]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #992]
	rev x8, x7
	str x8, [x5, #1000]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #1008]
	rev x8, x7
	str x8, [x5, #1016]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	str x6, [x5, #3248]
	str x7, [x5, #3256]
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	add x0, x5, #0
	movz x1, #396, lsl #0
	bl {vg_sm4_crypt_prepared}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	lsr x13, x24, #4
	cbnz x13, 23f
	add x16, x24, #0
	b 24f
23:
	movz x16, #16, lsl #0
24:
	add x14, x5, #0
	add x14, x14, #768
	add x15, x23, #0
	add x17, x16, #0
25:
	ldr x8, [x14, #0]
	ldr x9, [x15, #0]
	eor x8, x8, x9
	str x8, [x15, #0]
	ldr x8, [x14, #8]
	ldr x9, [x15, #8]
	eor x8, x8, x9
	str x8, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 25b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x19, [x5, #3168]
	ldr x20, [x5, #3176]
	ldr x21, [x5, #3184]
	ldr x22, [x5, #3192]
	ldr x23, [x5, #3200]
	ldr x24, [x5, #3208]
	ldr x25, [x5, #3216]
	ldr x26, [x5, #3224]
	ldr x27, [x5, #3232]
	ldr x28, [x5, #3240]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1536
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #2048
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #2560
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #3072
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add sp, sp, #3264
	ret
	.p2align 6

vg_sm4_gcm_init:
	sub sp, sp, #768
	add x2, sp, #0
	str x20, [x2, #136]
	str x21, [x2, #144]
	str x22, [x2, #152]
	str x23, [x2, #160]
	str x24, [x2, #168]
	str x25, [x2, #176]
	str x26, [x2, #184]
	str x27, [x2, #192]
	str x28, [x2, #200]
	str x30, [x2, #208]
	str x19, [x2, #128]
	add x19, x2, #0
	add x21, x1, #0
	bl {vg_sm4_expand_key}
	movz x9, #0, lsl #0
	str x9, [x21, #240]
	str x9, [x21, #248]
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x19, #96
	add x2, x21, #240
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
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
	add sp, sp, #768
	ret
	.p2align 6

vg_sm4_gcm_seal_aes:
	.arch_extension aes
	sub sp, sp, #784
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x19, #16
	add x21, x0, #0
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	str x7, [x19, #248]
	add x28, x7, #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 230f
	cbz x27, 232f
	movz x25, #0, lsl #0
	b 233f
232:
233:
	b 231f
230:
	movz x25, #0, lsl #0
231:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 234f
	lsr x14, x13, #2
	cbz x14, 236f
	lsr x14, x13, #3
	cbz x14, 238f
240:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 240b
	b 239f
238:
239:
	lsr x14, x13, #2
	cbz x14, 241f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 242f
241:
242:
	cbz x13, 243f
245:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	b 237f
236:
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
237:
	b 235f
234:
235:
	cbz x25, 247f
	movz x3, #1, lsl #0
	b 248f
247:
	movz x3, #0, lsl #0
248:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 249f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 251f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 253f
	add x10, x9, #0
	b 254f
253:
	add x10, x24, #0
254:
	b 252f
251:
	add x10, x9, #0
252:
	b 250f
249:
	movz x10, #0, lsl #0
250:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 255f
257:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 257b
	b 256f
255:
256:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 258f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 259f
258:
	movz x3, #0, lsl #0
259:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 260f
	lsr x14, x13, #2
	cbz x14, 262f
	lsr x14, x13, #3
	cbz x14, 264f
266:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 266b
	b 265f
264:
265:
	lsr x14, x13, #2
	cbz x14, 267f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 268f
267:
268:
	cbz x13, 269f
271:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 271b
	b 270f
269:
270:
	b 263f
262:
272:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
263:
	b 261f
260:
261:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 273f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 275f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 277f
	add x10, x9, #0
	b 278f
277:
	add x10, x24, #0
278:
	b 276f
275:
	add x10, x9, #0
276:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 279f
281:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 281b
	b 280f
279:
280:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 282f
	movz x3, #0, lsl #0
	b 283f
282:
	movz x3, #1, lsl #0
283:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 284f
	lsr x14, x13, #2
	cbz x14, 286f
	lsr x14, x13, #3
	cbz x14, 288f
290:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 290b
	b 289f
288:
289:
	lsr x14, x13, #2
	cbz x14, 291f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 292f
291:
292:
	cbz x13, 293f
295:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 295b
	b 294f
293:
294:
	b 287f
286:
296:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 296b
287:
	b 285f
284:
285:
	b 274f
273:
274:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 297f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 298f
297:
	movz x9, #15, lsl #0
	and x25, x26, x9
298:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 299f
	lsr x14, x13, #2
	cbz x14, 2101f
	lsr x14, x13, #3
	cbz x14, 2103f
2105:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2105b
	b 2104f
2103:
2104:
	lsr x14, x13, #2
	cbz x14, 2106f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2107f
2106:
2107:
	cbz x13, 2108f
2110:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2110b
	b 2109f
2108:
2109:
	b 2102f
2101:
2111:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2111b
2102:
	b 2100f
299:
2100:
	cbz x25, 2112f
	movz x3, #1, lsl #0
	b 2113f
2112:
	movz x3, #0, lsl #0
2113:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #0
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
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
	add sp, sp, #784
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_open_aes:
	.arch_extension aes
	sub sp, sp, #784
	add x16, sp, #0
	ldr x17, [sp, #784]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	ldr x9, [sp, #8]
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
	add x20, x19, #16
	add x21, x0, #0
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	add x12, x7, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	sub x9, x24, #12
	cbz x9, 27f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 28f
27:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
28:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 224f
	lsr x14, x13, #2
	cbz x14, 226f
	lsr x14, x13, #3
	cbz x14, 228f
230:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 230b
	b 229f
228:
229:
	lsr x14, x13, #2
	cbz x14, 231f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 232f
231:
232:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	b 227f
226:
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
227:
	b 225f
224:
225:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 237f
	cbz x27, 239f
	movz x25, #0, lsl #0
	b 240f
239:
240:
	b 238f
237:
	movz x25, #0, lsl #0
238:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 241f
	lsr x14, x13, #2
	cbz x14, 243f
	lsr x14, x13, #3
	cbz x14, 245f
247:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 247b
	b 246f
245:
246:
	lsr x14, x13, #2
	cbz x14, 248f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 249f
248:
249:
	cbz x13, 250f
252:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 252b
	b 251f
250:
251:
	b 244f
243:
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
244:
	b 242f
241:
242:
	cbz x25, 254f
	movz x3, #1, lsl #0
	b 255f
254:
	movz x3, #0, lsl #0
255:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 256f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 258f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 260f
	add x10, x9, #0
	b 261f
260:
	add x10, x24, #0
261:
	b 259f
258:
	add x10, x9, #0
259:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 262f
264:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 264b
	b 263f
262:
263:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 265f
	movz x3, #0, lsl #0
	b 266f
265:
	movz x3, #1, lsl #0
266:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 267f
	lsr x14, x13, #2
	cbz x14, 269f
	lsr x14, x13, #3
	cbz x14, 271f
273:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 273b
	b 272f
271:
272:
	lsr x14, x13, #2
	cbz x14, 274f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 275f
274:
275:
	cbz x13, 276f
278:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 278b
	b 277f
276:
277:
	b 270f
269:
279:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
270:
	b 268f
267:
268:
	b 257f
256:
257:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 280f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 281f
280:
	movz x9, #15, lsl #0
	and x25, x26, x9
281:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 282f
	lsr x14, x13, #2
	cbz x14, 284f
	lsr x14, x13, #3
	cbz x14, 286f
288:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 288b
	b 287f
286:
287:
	lsr x14, x13, #2
	cbz x14, 289f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 290f
289:
290:
	cbz x13, 291f
293:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 293b
	b 292f
291:
292:
	b 285f
284:
294:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 294b
285:
	b 283f
282:
283:
	cbz x25, 295f
	movz x3, #1, lsl #0
	b 296f
295:
	movz x3, #0, lsl #0
296:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #112
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 297f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 298f
297:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2102f
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
	b 2103f
2102:
2103:
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
298:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2105f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 2107f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2108f
2107:
	movz x3, #0, lsl #0
2108:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2109f
	lsr x14, x13, #2
	cbz x14, 2111f
	lsr x14, x13, #3
	cbz x14, 2113f
2115:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2115b
	b 2114f
2113:
2114:
	lsr x14, x13, #2
	cbz x14, 2116f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2117f
2116:
2117:
	cbz x13, 2118f
2120:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2120b
	b 2119f
2118:
2119:
	b 2112f
2111:
2121:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2121b
2112:
	b 2110f
2109:
2110:
	b 2106f
2105:
2106:
	add x0, x27, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	add sp, sp, #784
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_encrypt_aes:
	.arch_extension aes
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x5, #0
	add x27, x3, #0
	add x28, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	b 220f
219:
	movz x10, #0, lsl #0
220:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
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
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 228f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 229f
228:
	movz x3, #0, lsl #0
229:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 252f
	movz x3, #0, lsl #0
	b 253f
252:
	movz x3, #1, lsl #0
253:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	b 244f
243:
244:
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
	add sp, sp, #768
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_decrypt_aes:
	.arch_extension aes
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x5, #0
	add x27, x3, #0
	add x28, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 228f
	movz x3, #0, lsl #0
	b 229f
228:
	movz x3, #1, lsl #0
229:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	b 220f
219:
220:
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	b 244f
243:
	movz x10, #0, lsl #0
244:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 252f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 253f
252:
	movz x3, #0, lsl #0
253:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
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
	add sp, sp, #768
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_finish_aes:
	.arch_extension aes
	sub sp, sp, #768
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x2, #0
	add x27, x3, #0
	add x28, x4, #0
	cbz x27, 20f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 21f
20:
	movz x9, #15, lsl #0
	and x25, x26, x9
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #0
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
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
	add sp, sp, #768
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_verify_aes:
	.arch_extension aes
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x2, #0
	add x27, x3, #0
	add x28, x5, #0
	add x12, x4, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	cbz x27, 27f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 28f
27:
	movz x9, #15, lsl #0
	and x25, x26, x9
28:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #112
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	lsr x9, x28, #4
	cbz x9, 224f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 225f
224:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 229f
231:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 231b
	b 230f
229:
230:
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
225:
	movz x0, #1, lsl #0
	sub x0, x0, x10
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	add sp, sp, #768
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_init_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x4, sp, #0
	str x20, [x4, #136]
	str x21, [x4, #144]
	str x22, [x4, #152]
	str x23, [x4, #160]
	str x24, [x4, #168]
	str x25, [x4, #176]
	str x26, [x4, #184]
	str x27, [x4, #192]
	str x28, [x4, #200]
	str x30, [x4, #208]
	str x19, [x4, #128]
	add x19, x4, #0
	add x20, x3, #0
	add x21, x0, #0
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
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
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_stream_aad_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x23, x3, #0
	add x24, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 20f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 22f
	add x10, x9, #0
	b 23f
22:
	add x10, x24, #0
23:
	b 21f
20:
	add x10, x9, #0
21:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 27f
	movz x3, #0, lsl #0
	b 28f
27:
	movz x3, #1, lsl #0
28:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
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
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_sm4_gcm_seal:
	sub sp, sp, #784
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x19, #16
	add x21, x0, #0
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	str x7, [x19, #248]
	add x28, x7, #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 230f
	cbz x27, 232f
	movz x25, #0, lsl #0
	b 233f
232:
233:
	b 231f
230:
	movz x25, #0, lsl #0
231:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 234f
	lsr x14, x13, #2
	cbz x14, 236f
	lsr x14, x13, #3
	cbz x14, 238f
240:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 240b
	b 239f
238:
239:
	lsr x14, x13, #2
	cbz x14, 241f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 242f
241:
242:
	cbz x13, 243f
245:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	b 237f
236:
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
237:
	b 235f
234:
235:
	cbz x25, 247f
	movz x3, #1, lsl #0
	b 248f
247:
	movz x3, #0, lsl #0
248:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 249f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 251f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 253f
	add x10, x9, #0
	b 254f
253:
	add x10, x24, #0
254:
	b 252f
251:
	add x10, x9, #0
252:
	b 250f
249:
	movz x10, #0, lsl #0
250:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 255f
257:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 257b
	b 256f
255:
256:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 258f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 259f
258:
	movz x3, #0, lsl #0
259:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 260f
	lsr x14, x13, #2
	cbz x14, 262f
	lsr x14, x13, #3
	cbz x14, 264f
266:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 266b
	b 265f
264:
265:
	lsr x14, x13, #2
	cbz x14, 267f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 268f
267:
268:
	cbz x13, 269f
271:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 271b
	b 270f
269:
270:
	b 263f
262:
272:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
263:
	b 261f
260:
261:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 273f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 275f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 277f
	add x10, x9, #0
	b 278f
277:
	add x10, x24, #0
278:
	b 276f
275:
	add x10, x9, #0
276:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 279f
281:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 281b
	b 280f
279:
280:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 282f
	movz x3, #0, lsl #0
	b 283f
282:
	movz x3, #1, lsl #0
283:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 284f
	lsr x14, x13, #2
	cbz x14, 286f
	lsr x14, x13, #3
	cbz x14, 288f
290:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 290b
	b 289f
288:
289:
	lsr x14, x13, #2
	cbz x14, 291f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 292f
291:
292:
	cbz x13, 293f
295:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 295b
	b 294f
293:
294:
	b 287f
286:
296:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 296b
287:
	b 285f
284:
285:
	b 274f
273:
274:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 297f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 298f
297:
	movz x9, #15, lsl #0
	and x25, x26, x9
298:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 299f
	lsr x14, x13, #2
	cbz x14, 2101f
	lsr x14, x13, #3
	cbz x14, 2103f
2105:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2105b
	b 2104f
2103:
2104:
	lsr x14, x13, #2
	cbz x14, 2106f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2107f
2106:
2107:
	cbz x13, 2108f
2110:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2110b
	b 2109f
2108:
2109:
	b 2102f
2101:
2111:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2111b
2102:
	b 2100f
299:
2100:
	cbz x25, 2112f
	movz x3, #1, lsl #0
	b 2113f
2112:
	movz x3, #0, lsl #0
2113:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #0
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
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
	add sp, sp, #784
	ret
	.p2align 6

vg_sm4_gcm_open:
	sub sp, sp, #784
	add x16, sp, #0
	ldr x17, [sp, #784]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	ldr x9, [sp, #8]
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
	add x20, x19, #16
	add x21, x0, #0
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	add x12, x7, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	sub x9, x24, #12
	cbz x9, 27f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 28f
27:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
28:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 224f
	lsr x14, x13, #2
	cbz x14, 226f
	lsr x14, x13, #3
	cbz x14, 228f
230:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 230b
	b 229f
228:
229:
	lsr x14, x13, #2
	cbz x14, 231f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 232f
231:
232:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	b 227f
226:
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
227:
	b 225f
224:
225:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 237f
	cbz x27, 239f
	movz x25, #0, lsl #0
	b 240f
239:
240:
	b 238f
237:
	movz x25, #0, lsl #0
238:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 241f
	lsr x14, x13, #2
	cbz x14, 243f
	lsr x14, x13, #3
	cbz x14, 245f
247:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 247b
	b 246f
245:
246:
	lsr x14, x13, #2
	cbz x14, 248f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 249f
248:
249:
	cbz x13, 250f
252:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 252b
	b 251f
250:
251:
	b 244f
243:
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
244:
	b 242f
241:
242:
	cbz x25, 254f
	movz x3, #1, lsl #0
	b 255f
254:
	movz x3, #0, lsl #0
255:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 256f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 258f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 260f
	add x10, x9, #0
	b 261f
260:
	add x10, x24, #0
261:
	b 259f
258:
	add x10, x9, #0
259:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 262f
264:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 264b
	b 263f
262:
263:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 265f
	movz x3, #0, lsl #0
	b 266f
265:
	movz x3, #1, lsl #0
266:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 267f
	lsr x14, x13, #2
	cbz x14, 269f
	lsr x14, x13, #3
	cbz x14, 271f
273:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 273b
	b 272f
271:
272:
	lsr x14, x13, #2
	cbz x14, 274f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 275f
274:
275:
	cbz x13, 276f
278:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 278b
	b 277f
276:
277:
	b 270f
269:
279:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
270:
	b 268f
267:
268:
	b 257f
256:
257:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 280f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 281f
280:
	movz x9, #15, lsl #0
	and x25, x26, x9
281:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 282f
	lsr x14, x13, #2
	cbz x14, 284f
	lsr x14, x13, #3
	cbz x14, 286f
288:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 288b
	b 287f
286:
287:
	lsr x14, x13, #2
	cbz x14, 289f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 290f
289:
290:
	cbz x13, 291f
293:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 293b
	b 292f
291:
292:
	b 285f
284:
294:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 294b
285:
	b 283f
282:
283:
	cbz x25, 295f
	movz x3, #1, lsl #0
	b 296f
295:
	movz x3, #0, lsl #0
296:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #112
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 297f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 298f
297:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2102f
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
	b 2103f
2102:
2103:
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
298:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2105f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 2107f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2108f
2107:
	movz x3, #0, lsl #0
2108:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2109f
	lsr x14, x13, #2
	cbz x14, 2111f
	lsr x14, x13, #3
	cbz x14, 2113f
2115:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2115b
	b 2114f
2113:
2114:
	lsr x14, x13, #2
	cbz x14, 2116f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2117f
2116:
2117:
	cbz x13, 2118f
2120:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2120b
	b 2119f
2118:
2119:
	b 2112f
2111:
2121:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2121b
2112:
	b 2110f
2109:
2110:
	b 2106f
2105:
2106:
	add x0, x27, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	add sp, sp, #784
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt:
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x5, #0
	add x27, x3, #0
	add x28, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	b 220f
219:
	movz x10, #0, lsl #0
220:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
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
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 228f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 229f
228:
	movz x3, #0, lsl #0
229:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 252f
	movz x3, #0, lsl #0
	b 253f
252:
	movz x3, #1, lsl #0
253:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	b 244f
243:
244:
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
	add sp, sp, #768
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt:
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x5, #0
	add x27, x3, #0
	add x28, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 228f
	movz x3, #0, lsl #0
	b 229f
228:
	movz x3, #1, lsl #0
229:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	b 220f
219:
220:
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	b 244f
243:
	movz x10, #0, lsl #0
244:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 252f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 253f
252:
	movz x3, #0, lsl #0
253:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
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
	add sp, sp, #768
	ret
	.p2align 6

vg_sm4_gcm_stream_finish:
	sub sp, sp, #768
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x2, #0
	add x27, x3, #0
	add x28, x4, #0
	cbz x27, 20f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 21f
20:
	movz x9, #15, lsl #0
	and x25, x26, x9
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #0
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
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
	add sp, sp, #768
	ret
	.p2align 6

vg_sm4_gcm_stream_verify:
	sub sp, sp, #768
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x1, #0
	add x21, x0, #0
	add x26, x2, #0
	add x27, x3, #0
	add x28, x5, #0
	add x12, x4, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	cbz x27, 27f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 28f
27:
	movz x9, #15, lsl #0
	and x25, x26, x9
28:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #112
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
	lsr x9, x28, #4
	cbz x9, 224f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 225f
224:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 229f
231:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 231b
	b 230f
229:
230:
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
225:
	movz x0, #1, lsl #0
	sub x0, x0, x10
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	add sp, sp, #768
	ret
	.p2align 6

vg_sm4_gcm_stream_init:
	sub sp, sp, #2560
	add x4, sp, #0
	str x20, [x4, #136]
	str x21, [x4, #144]
	str x22, [x4, #152]
	str x23, [x4, #160]
	str x24, [x4, #168]
	str x25, [x4, #176]
	str x26, [x4, #184]
	str x27, [x4, #192]
	str x28, [x4, #200]
	str x30, [x4, #208]
	str x19, [x4, #128]
	add x19, x4, #0
	add x20, x3, #0
	add x21, x0, #0
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
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
	add sp, sp, #2560
	ret
	.p2align 6

vg_sm4_gcm_stream_aad:
	sub sp, sp, #2560
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x23, x3, #0
	add x24, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 20f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 22f
	add x10, x9, #0
	b 23f
22:
	add x10, x24, #0
23:
	b 21f
20:
	add x10, x9, #0
21:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 27f
	movz x3, #0, lsl #0
	b 28f
27:
	movz x3, #1, lsl #0
28:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
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
	add sp, sp, #2560
	ret
	.p2align 6
