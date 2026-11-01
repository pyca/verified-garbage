// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
