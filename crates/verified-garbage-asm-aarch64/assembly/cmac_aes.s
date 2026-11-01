// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_update_aes_cbc:
	.arch_extension aes
	cbz x4, 20f
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q24, [x0, #128]
	ldr q25, [x0, #144]
	ldr q26, [x0, #160]
	ldr q27, [x0, #176]
	ldr q28, [x0, #192]
	lsl x9, x1, #4
	add x9, x0, x9
	ldr q30, [x9, #0]
	sub x9, x9, #16
	ldr q29, [x9, #0]
	sub x6, x1, #10
	sub x7, x1, #12
	ldr q0, [x2, #0]
	eor v31.16b, v16.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	cbz x6, 22f
	cbz x7, 24f
26:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 26b
	b 25f
24:
27:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 27b
25:
	b 23f
22:
28:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 28b
23:
	eor v0.16b, v0.16b, v30.16b
	str q0, [x2, #0]
	b 21f
20:
21:
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_subkeys_aes:
	.arch_extension aes
	str x19, [x3, #2064]
	str x20, [x3, #2072]
	str x30, [x3, #2080]
	add x19, x2, #0
	add x20, x3, #0
	movz x9, #0, lsl #0
	str x9, [x3, #2048]
	str x9, [x3, #2056]
	str x9, [x2, #0]
	str x9, [x2, #8]
	add x2, x20, #2048
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
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
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
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
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x30, [x20, #2080]
	ldr x19, [x20, #2064]
	ldr x20, [x20, #2072]
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_update_aes:
	.arch_extension aes
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
22:
	ldr x9, [x21, #0]
	ldr x10, [x22, #0]
	eor x9, x9, x10
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	ldr x10, [x22, #8]
	eor x9, x9, x10
	str x9, [x24, #2056]
	movz x9, #0, lsl #0
	str x9, [x21, #0]
	str x9, [x21, #8]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	add x3, x21, #0
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_ctr32_aes}
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_finalize_aes:
	.arch_extension aes
	sub x9, x4, #16
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x5, #2048]
	str x9, [x5, #2056]
	add x6, x5, #2048
	add x7, x3, #0
	add x8, x4, #0
	cbz x4, 22f
24:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 24b
	b 23f
22:
23:
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x5, #2048]
	ldr x10, [x0, #256]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x5, #2056]
	ldr x10, [x0, #264]
	eor x9, x9, x10
	str x9, [x5, #2056]
	b 21f
20:
	ldr x9, [x3, #0]
	ldr x10, [x0, #240]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x3, #8]
	ldr x10, [x0, #248]
	eor x9, x9, x10
	str x9, [x5, #2056]
21:
	ldr x9, [x5, #2048]
	ldr x10, [x2, #0]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x5, #2056]
	ldr x10, [x2, #8]
	eor x9, x9, x10
	str x9, [x5, #2056]
	movz x9, #0, lsl #0
	str x9, [x2, #0]
	str x9, [x2, #8]
	str x19, [x5, #2064]
	str x30, [x5, #2072]
	add x19, x5, #0
	add x3, x2, #0
	add x2, x5, #2048
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32_aes}
	ldr x30, [x19, #2072]
	ldr x19, [x19, #2064]
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_init_aes:
	.arch_extension aes
	sub sp, sp, #2304
	add x3, sp, #0
	str x19, [x3, #2176]
	str x20, [x3, #2184]
	str x21, [x3, #2192]
	str x30, [x3, #2200]
	add x19, x0, #0
	add x20, x3, #0
	lsr x21, x2, #2
	add x21, x21, #6
	add x0, x1, #0
	add x1, x2, #0
	add x2, x19, #0
	bl {vg_aes_expand_key_scratch_aes}
	add x0, x19, #0
	add x1, x21, #0
	add x2, x19, #240
	add x3, x20, #0
	bl {vg_cmac_aes_subkeys_aes}
	movz x9, #0, lsl #0
	str x9, [x19, #272]
	str x9, [x19, #280]
	ldr x30, [x20, #2200]
	ldr x19, [x20, #2176]
	ldr x21, [x20, #2192]
	ldr x20, [x20, #2184]
	add sp, sp, #2304
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_finish_aes:
	.arch_extension aes
	sub sp, sp, #2304
	add x4, sp, #0
	ldr x9, [x0, #272]
	str x9, [x3, #0]
	ldr x9, [x0, #280]
	str x9, [x3, #8]
	str x19, [x4, #2176]
	str x30, [x4, #2184]
	add x19, x4, #0
	add x5, x4, #0
	add x4, x2, #0
	add x2, x3, #0
	add x3, x0, #288
	cbz x4, 20f
	sub x4, x4, #1
	movz x9, #15, lsl #0
	and x4, x4, x9
	add x4, x4, #1
	b 21f
20:
21:
	bl {vg_cmac_aes_finalize_aes}
	ldr x30, [x19, #2184]
	ldr x19, [x19, #2176]
	add sp, sp, #2304
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_subkeys:
	str x19, [x3, #2064]
	str x20, [x3, #2072]
	str x30, [x3, #2080]
	add x19, x2, #0
	add x20, x3, #0
	movz x9, #0, lsl #0
	str x9, [x3, #2048]
	str x9, [x3, #2056]
	str x9, [x2, #0]
	str x9, [x2, #8]
	add x2, x20, #2048
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_aes_ctr32}
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
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
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
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
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x30, [x20, #2080]
	ldr x19, [x20, #2064]
	ldr x20, [x20, #2072]
	ret
	.p2align 6

vg_cmac_aes_update:
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
22:
	ldr x9, [x21, #0]
	ldr x10, [x22, #0]
	eor x9, x9, x10
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	ldr x10, [x22, #8]
	eor x9, x9, x10
	str x9, [x24, #2056]
	movz x9, #0, lsl #0
	str x9, [x21, #0]
	str x9, [x21, #8]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	add x3, x21, #0
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_ctr32}
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	ret
	.p2align 6

vg_cmac_aes_finalize:
	sub x9, x4, #16
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x5, #2048]
	str x9, [x5, #2056]
	add x6, x5, #2048
	add x7, x3, #0
	add x8, x4, #0
	cbz x4, 22f
24:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 24b
	b 23f
22:
23:
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x5, #2048]
	ldr x10, [x0, #256]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x5, #2056]
	ldr x10, [x0, #264]
	eor x9, x9, x10
	str x9, [x5, #2056]
	b 21f
20:
	ldr x9, [x3, #0]
	ldr x10, [x0, #240]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x3, #8]
	ldr x10, [x0, #248]
	eor x9, x9, x10
	str x9, [x5, #2056]
21:
	ldr x9, [x5, #2048]
	ldr x10, [x2, #0]
	eor x9, x9, x10
	str x9, [x5, #2048]
	ldr x9, [x5, #2056]
	ldr x10, [x2, #8]
	eor x9, x9, x10
	str x9, [x5, #2056]
	movz x9, #0, lsl #0
	str x9, [x2, #0]
	str x9, [x2, #8]
	str x19, [x5, #2064]
	str x30, [x5, #2072]
	add x19, x5, #0
	add x3, x2, #0
	add x2, x5, #2048
	movz x4, #1, lsl #0
	bl {vg_aes_ctr32}
	ldr x30, [x19, #2072]
	ldr x19, [x19, #2064]
	ret
	.p2align 6

vg_cmac_aes_init:
	sub sp, sp, #2304
	add x3, sp, #0
	str x19, [x3, #2176]
	str x20, [x3, #2184]
	str x21, [x3, #2192]
	str x30, [x3, #2200]
	add x19, x0, #0
	add x20, x3, #0
	lsr x21, x2, #2
	add x21, x21, #6
	add x0, x1, #0
	add x1, x2, #0
	add x2, x19, #0
	bl {vg_aes_expand_key_scratch}
	add x0, x19, #0
	add x1, x21, #0
	add x2, x19, #240
	add x3, x20, #0
	bl {vg_cmac_aes_subkeys}
	movz x9, #0, lsl #0
	str x9, [x19, #272]
	str x9, [x19, #280]
	ldr x30, [x20, #2200]
	ldr x19, [x20, #2176]
	ldr x21, [x20, #2192]
	ldr x20, [x20, #2184]
	add sp, sp, #2304
	ret
	.p2align 6

vg_cmac_aes_finish:
	sub sp, sp, #2304
	add x4, sp, #0
	ldr x9, [x0, #272]
	str x9, [x3, #0]
	ldr x9, [x0, #280]
	str x9, [x3, #8]
	str x19, [x4, #2176]
	str x30, [x4, #2184]
	add x19, x4, #0
	add x5, x4, #0
	add x4, x2, #0
	add x2, x3, #0
	add x3, x0, #288
	cbz x4, 20f
	sub x4, x4, #1
	movz x9, #15, lsl #0
	and x4, x4, x9
	add x4, x4, #1
	b 21f
20:
21:
	bl {vg_cmac_aes_finalize}
	ldr x30, [x19, #2184]
	ldr x19, [x19, #2176]
	add sp, sp, #2304
	ret
	.p2align 6

vg_cmac_aes_absorb_aes:
	.arch_extension aes
	sub sp, sp, #2304
	add x5, sp, #0
	str x19, [x5, #2176]
	str x20, [x5, #2184]
	str x21, [x5, #2192]
	str x22, [x5, #2200]
	str x24, [x5, #2208]
	str x30, [x5, #2216]
	str x23, [x5, #2224]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	cbz x2, 20f
	sub x9, x2, #1
	movz x10, #15, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	b 21f
20:
	movz x9, #0, lsl #0
21:
	lsr x10, x22, #4
	cbz x10, 22f
	movz x10, #16, lsl #0
	b 23f
22:
	add x10, x22, #0
23:
	movz x8, #16, lsl #0
	sub x8, x8, x9
	sub x11, x10, x8
	lsr x11, x11, #63
	cbz x11, 24f
	add x8, x10, #0
	b 25f
24:
25:
	add x10, x8, #0
	add x6, x19, x9
	add x6, x6, #288
	add x7, x21, #0
	cbz x8, 26f
28:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 28b
	b 27f
26:
27:
	add x21, x21, x10
	sub x22, x22, x10
	movz x4, #0, lsl #0
	cbz x22, 29f
	movz x4, #1, lsl #0
	b 210f
29:
210:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x19, #288
	add x5, x23, #0
	bl {vg_cmac_aes_update_aes}
	movz x24, #0, lsl #0
	cbz x22, 211f
	sub x24, x22, #1
	movz x9, #15, lsl #0
	and x9, x24, x9
	sub x24, x24, x9
	b 212f
211:
212:
	lsr x4, x24, #4
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x21, #0
	add x5, x23, #0
	bl {vg_cmac_aes_update_aes}
	add x21, x21, x24
	sub x22, x22, x24
	add x6, x19, #288
	add x7, x21, #0
	add x8, x22, #0
	cbz x8, 213f
215:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 215b
	b 214f
213:
214:
	ldr x19, [x23, #2176]
	ldr x20, [x23, #2184]
	ldr x21, [x23, #2192]
	ldr x22, [x23, #2200]
	ldr x24, [x23, #2208]
	ldr x30, [x23, #2216]
	ldr x23, [x23, #2224]
	add sp, sp, #2304
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_absorb_aes_cbc:
	.arch_extension aes
	sub sp, sp, #2304
	add x5, sp, #0
	str x19, [x5, #2176]
	str x20, [x5, #2184]
	str x21, [x5, #2192]
	str x22, [x5, #2200]
	str x24, [x5, #2208]
	str x30, [x5, #2216]
	str x23, [x5, #2224]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	cbz x2, 20f
	sub x9, x2, #1
	movz x10, #15, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	b 21f
20:
	movz x9, #0, lsl #0
21:
	lsr x10, x22, #4
	cbz x10, 22f
	movz x10, #16, lsl #0
	b 23f
22:
	add x10, x22, #0
23:
	movz x8, #16, lsl #0
	sub x8, x8, x9
	sub x11, x10, x8
	lsr x11, x11, #63
	cbz x11, 24f
	add x8, x10, #0
	b 25f
24:
25:
	add x10, x8, #0
	add x6, x19, x9
	add x6, x6, #288
	add x7, x21, #0
	cbz x8, 26f
28:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 28b
	b 27f
26:
27:
	add x21, x21, x10
	sub x22, x22, x10
	movz x4, #0, lsl #0
	cbz x22, 29f
	movz x4, #1, lsl #0
	b 210f
29:
210:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x19, #288
	add x5, x23, #0
	bl {vg_cmac_aes_update_aes_cbc}
	movz x24, #0, lsl #0
	cbz x22, 211f
	sub x24, x22, #1
	movz x9, #15, lsl #0
	and x9, x24, x9
	sub x24, x24, x9
	b 212f
211:
212:
	lsr x4, x24, #4
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x21, #0
	add x5, x23, #0
	bl {vg_cmac_aes_update_aes_cbc}
	add x21, x21, x24
	sub x22, x22, x24
	add x6, x19, #288
	add x7, x21, #0
	add x8, x22, #0
	cbz x8, 213f
215:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 215b
	b 214f
213:
214:
	ldr x19, [x23, #2176]
	ldr x20, [x23, #2184]
	ldr x21, [x23, #2192]
	ldr x22, [x23, #2200]
	ldr x24, [x23, #2208]
	ldr x30, [x23, #2216]
	ldr x23, [x23, #2224]
	add sp, sp, #2304
	ret
	.arch_extension noaes
	.p2align 6

vg_cmac_aes_absorb:
	sub sp, sp, #2304
	add x5, sp, #0
	str x19, [x5, #2176]
	str x20, [x5, #2184]
	str x21, [x5, #2192]
	str x22, [x5, #2200]
	str x24, [x5, #2208]
	str x30, [x5, #2216]
	str x23, [x5, #2224]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	cbz x2, 20f
	sub x9, x2, #1
	movz x10, #15, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	b 21f
20:
	movz x9, #0, lsl #0
21:
	lsr x10, x22, #4
	cbz x10, 22f
	movz x10, #16, lsl #0
	b 23f
22:
	add x10, x22, #0
23:
	movz x8, #16, lsl #0
	sub x8, x8, x9
	sub x11, x10, x8
	lsr x11, x11, #63
	cbz x11, 24f
	add x8, x10, #0
	b 25f
24:
25:
	add x10, x8, #0
	add x6, x19, x9
	add x6, x6, #288
	add x7, x21, #0
	cbz x8, 26f
28:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 28b
	b 27f
26:
27:
	add x21, x21, x10
	sub x22, x22, x10
	movz x4, #0, lsl #0
	cbz x22, 29f
	movz x4, #1, lsl #0
	b 210f
29:
210:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x19, #288
	add x5, x23, #0
	bl {vg_cmac_aes_update}
	movz x24, #0, lsl #0
	cbz x22, 211f
	sub x24, x22, #1
	movz x9, #15, lsl #0
	and x9, x24, x9
	sub x24, x24, x9
	b 212f
211:
212:
	lsr x4, x24, #4
	add x0, x19, #0
	add x1, x20, #0
	add x2, x19, #272
	add x3, x21, #0
	add x5, x23, #0
	bl {vg_cmac_aes_update}
	add x21, x21, x24
	sub x22, x22, x24
	add x6, x19, #288
	add x7, x21, #0
	add x8, x22, #0
	cbz x8, 213f
215:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 215b
	b 214f
213:
214:
	ldr x19, [x23, #2176]
	ldr x20, [x23, #2184]
	ldr x21, [x23, #2192]
	ldr x22, [x23, #2200]
	ldr x24, [x23, #2208]
	ldr x30, [x23, #2216]
	ldr x23, [x23, #2224]
	add sp, sp, #2304
	ret
	.p2align 6
