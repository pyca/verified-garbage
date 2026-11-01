// The functions of `src/aes_cfb8.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb8_encrypt_aes:
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
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	str x9, [x24, #2056]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	ldrb w9, [x22, #0]
	ldrb w10, [x24, #2048]
	eor x9, x9, x10
	strb w9, [x22, #0]
	ldr x10, [x21, #0]
	ldr x11, [x21, #8]
	extr x12, x11, x10, #8
	extr x13, x9, x11, #8
	str x12, [x21, #0]
	str x13, [x21, #8]
	add x22, x22, #1
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

vg_aes_cfb8_decrypt_aes:
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
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	str x9, [x24, #2056]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	ldrb w9, [x22, #0]
	ldrb w10, [x24, #2048]
	eor x10, x10, x9
	strb w10, [x22, #0]
	ldr x10, [x21, #0]
	ldr x11, [x21, #8]
	extr x12, x11, x10, #8
	extr x13, x9, x11, #8
	str x12, [x21, #0]
	str x13, [x21, #8]
	add x22, x22, #1
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

vg_aes_cfb8_encrypt:
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
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	str x9, [x24, #2056]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldrb w9, [x22, #0]
	ldrb w10, [x24, #2048]
	eor x9, x9, x10
	strb w9, [x22, #0]
	ldr x10, [x21, #0]
	ldr x11, [x21, #8]
	extr x12, x11, x10, #8
	extr x13, x9, x11, #8
	str x12, [x21, #0]
	str x13, [x21, #8]
	add x22, x22, #1
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

vg_aes_cfb8_decrypt:
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
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	str x9, [x24, #2056]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldrb w9, [x22, #0]
	ldrb w10, [x24, #2048]
	eor x10, x10, x9
	strb w10, [x22, #0]
	ldr x10, [x21, #0]
	ldr x11, [x21, #8]
	extr x12, x11, x10, #8
	extr x13, x9, x11, #8
	str x12, [x21, #0]
	str x13, [x21, #8]
	add x22, x22, #1
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
