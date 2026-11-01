// The functions of `src/aes_xts.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_unit_aes:
	.arch_extension aes
	str x19, [x6, #2208]
	str x20, [x6, #2216]
	str x21, [x6, #2224]
	str x22, [x6, #2232]
	str x23, [x6, #2240]
	str x30, [x6, #2248]
	str x24, [x6, #2256]
	add x24, x6, #0
	add x19, x0, #0
	add x20, x2, #0
	add x23, x4, #0
	add x22, x5, #0
	ldr x9, [x3, #0]
	str x9, [x24, #2176]
	ldr x9, [x3, #8]
	str x9, [x24, #2184]
	movz x9, #0, lsl #0
	str x9, [x24, #2192]
	str x9, [x24, #2200]
	add x0, x1, #0
	add x1, x20, #0
	add x2, x24, #2192
	add x3, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt_aes}
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	bl {vg_aes_xts_encrypt_aes}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	cbz x10, 20f
	add x11, x23, x9
	sub x11, x11, #16
22:
	ldrb w13, [x11, #0]
	ldrb w14, [x11, #16]
	strb w14, [x11, #0]
	strb w13, [x11, #16]
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 22b
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt_aes}
	b 21f
20:
21:
	ldr x19, [x24, #2208]
	ldr x20, [x24, #2216]
	ldr x21, [x24, #2224]
	ldr x22, [x24, #2232]
	ldr x23, [x24, #2240]
	ldr x30, [x24, #2248]
	ldr x24, [x24, #2256]
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_xts_decrypt_unit_aes:
	.arch_extension aes
	str x19, [x6, #2208]
	str x20, [x6, #2216]
	str x21, [x6, #2224]
	str x22, [x6, #2232]
	str x23, [x6, #2240]
	str x30, [x6, #2248]
	str x24, [x6, #2256]
	add x24, x6, #0
	add x19, x0, #0
	add x20, x2, #0
	add x23, x4, #0
	add x22, x5, #0
	ldr x9, [x3, #0]
	str x9, [x24, #2176]
	ldr x9, [x3, #8]
	str x9, [x24, #2184]
	movz x9, #0, lsl #0
	str x9, [x24, #2192]
	str x9, [x24, #2200]
	add x0, x1, #0
	add x1, x20, #0
	add x2, x24, #2192
	add x3, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt_aes}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	cbz x10, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	sub x4, x4, #1
	bl {vg_aes_xts_decrypt_aes}
	add x21, x24, #2192
	ldr x9, [x24, #2176]
	str x9, [x24, #2192]
	ldr x9, [x24, #2184]
	str x9, [x24, #2200]
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	adds x9, x9, x9
	adcs x10, x10, x10
	movz x11, #135, lsl #0
	movz x12, #0, lsl #0
	csel x11, x11, x12, hs
	eor x9, x9, x11
	str x9, [x21, #0]
	str x10, [x21, #8]
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2192
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_decrypt_aes}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	add x11, x23, x9
	sub x11, x11, #16
22:
	ldrb w13, [x11, #0]
	ldrb w14, [x11, #16]
	strb w14, [x11, #0]
	strb w13, [x11, #16]
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 22b
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_decrypt_aes}
	b 21f
20:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	bl {vg_aes_xts_decrypt_aes}
21:
	ldr x19, [x24, #2208]
	ldr x20, [x24, #2216]
	ldr x21, [x24, #2224]
	ldr x22, [x24, #2232]
	ldr x23, [x24, #2240]
	ldr x30, [x24, #2248]
	ldr x24, [x24, #2256]
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_xts_encrypt_unit:
	str x19, [x6, #2208]
	str x20, [x6, #2216]
	str x21, [x6, #2224]
	str x22, [x6, #2232]
	str x23, [x6, #2240]
	str x30, [x6, #2248]
	str x24, [x6, #2256]
	add x24, x6, #0
	add x19, x0, #0
	add x20, x2, #0
	add x23, x4, #0
	add x22, x5, #0
	ldr x9, [x3, #0]
	str x9, [x24, #2176]
	ldr x9, [x3, #8]
	str x9, [x24, #2184]
	movz x9, #0, lsl #0
	str x9, [x24, #2192]
	str x9, [x24, #2200]
	add x0, x1, #0
	add x1, x20, #0
	add x2, x24, #2192
	add x3, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt}
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	bl {vg_aes_xts_encrypt}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	cbz x10, 20f
	add x11, x23, x9
	sub x11, x11, #16
22:
	ldrb w13, [x11, #0]
	ldrb w14, [x11, #16]
	strb w14, [x11, #0]
	strb w13, [x11, #16]
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 22b
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt}
	b 21f
20:
21:
	ldr x19, [x24, #2208]
	ldr x20, [x24, #2216]
	ldr x21, [x24, #2224]
	ldr x22, [x24, #2232]
	ldr x23, [x24, #2240]
	ldr x30, [x24, #2248]
	ldr x24, [x24, #2256]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit:
	str x19, [x6, #2208]
	str x20, [x6, #2216]
	str x21, [x6, #2224]
	str x22, [x6, #2232]
	str x23, [x6, #2240]
	str x30, [x6, #2248]
	str x24, [x6, #2256]
	add x24, x6, #0
	add x19, x0, #0
	add x20, x2, #0
	add x23, x4, #0
	add x22, x5, #0
	ldr x9, [x3, #0]
	str x9, [x24, #2176]
	ldr x9, [x3, #8]
	str x9, [x24, #2184]
	movz x9, #0, lsl #0
	str x9, [x24, #2192]
	str x9, [x24, #2200]
	add x0, x1, #0
	add x1, x20, #0
	add x2, x24, #2192
	add x3, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_encrypt}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	cbz x10, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	sub x4, x4, #1
	bl {vg_aes_xts_decrypt}
	add x21, x24, #2192
	ldr x9, [x24, #2176]
	str x9, [x24, #2192]
	ldr x9, [x24, #2184]
	str x9, [x24, #2200]
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	adds x9, x9, x9
	adcs x10, x10, x10
	movz x11, #135, lsl #0
	movz x12, #0, lsl #0
	csel x11, x11, x12, hs
	eor x9, x9, x11
	str x9, [x21, #0]
	str x10, [x21, #8]
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2192
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_decrypt}
	lsr x9, x22, #4
	lsl x9, x9, #4
	sub x10, x22, x9
	add x11, x23, x9
	sub x11, x11, #16
22:
	ldrb w13, [x11, #0]
	ldrb w14, [x11, #16]
	strb w14, [x11, #0]
	strb w13, [x11, #16]
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 22b
	add x3, x23, x9
	sub x3, x3, #16
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_xts_decrypt}
	b 21f
20:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2176
	add x3, x23, #0
	lsr x4, x22, #4
	add x5, x24, #0
	bl {vg_aes_xts_decrypt}
21:
	ldr x19, [x24, #2208]
	ldr x20, [x24, #2216]
	ldr x21, [x24, #2224]
	ldr x22, [x24, #2232]
	ldr x23, [x24, #2240]
	ldr x30, [x24, #2248]
	ldr x24, [x24, #2256]
	ret
	.p2align 6
