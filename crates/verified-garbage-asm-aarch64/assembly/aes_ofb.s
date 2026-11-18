// The functions of `src/aes_ofb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb_aes:
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
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
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

vg_aes_ofb_final_aes:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_ofb_aes}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_ofb_neon:
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
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
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

vg_aes_ofb_final_neon:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_ofb_neon}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_neon}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_ofb:
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
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
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

vg_aes_ofb_final:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_ofb}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6
