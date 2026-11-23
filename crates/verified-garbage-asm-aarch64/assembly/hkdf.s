// The functions of `src/hkdf.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hkdf_key:
	str x30, [sp, #-16]!
	sub sp, sp, #3408
	ldr x16, [x3, #0]
	add x3, x1, #0
	add x9, x0, #0
	add x0, x2, #0
	add x1, x2, #192
	add x2, x9, #0
	add x4, sp, #0
	blr x16
	add sp, sp, #3408
	ldr x30, [sp], #16
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
	sub sp, sp, #3440
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #53, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #3440
	ret
	.p2align 6

vg_hkdf_extract:
	str x30, [sp, #-16]!
	sub sp, sp, #3824
	add x9, sp, #0
	str x19, [x9, #0]
	str x20, [x9, #8]
	str x21, [x9, #16]
	str x22, [x9, #24]
	add x19, x2, #0
	add x20, x3, #0
	add x21, x4, #0
	add x22, x6, #0
	add x2, x0, #0
	add x3, x1, #0
	add x0, sp, #32
	add x1, sp, #224
	add x4, sp, #416
	ldr x16, [x22, #0]
	blr x16
	add x0, sp, #32
	ldr x1, [x22, #40]
	add x2, x19, #0
	add x3, x20, #0
	add x4, sp, #416
	ldr x16, [x22, #8]
	blr x16
	add x0, sp, #32
	add x1, sp, #224
	ldr x2, [x22, #40]
	add x2, x2, x20
	add x3, x21, #0
	add x4, sp, #416
	ldr x16, [x22, #16]
	blr x16
	add x9, sp, #0
	ldr x19, [x9, #0]
	ldr x20, [x9, #8]
	ldr x21, [x9, #16]
	ldr x22, [x9, #24]
	add sp, sp, #3824
	ldr x30, [sp], #16
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
	sub sp, sp, #3856
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #60, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #3856
	ret
	.p2align 6

vg_hkdf_expand:
	str x30, [sp, #-16]!
	sub sp, sp, #2208
	add x9, sp, #0
	str x19, [x9, #0]
	str x20, [x9, #8]
	str x21, [x9, #16]
	str x22, [x9, #24]
	str x23, [x9, #32]
	str x24, [x9, #40]
	str x25, [x9, #48]
	str x26, [x9, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	movz x25, #1, lsl #0
	movz x26, #0, lsl #0
	cbnz x23, 20f
	b 21f
20:
22:
	ldr x9, [x19, #0]
	str x9, [sp, #64]
	ldr x9, [x19, #8]
	str x9, [sp, #72]
	ldr x9, [x19, #16]
	str x9, [sp, #80]
	ldr x9, [x19, #24]
	str x9, [sp, #88]
	ldr x9, [x19, #32]
	str x9, [sp, #96]
	ldr x9, [x19, #40]
	str x9, [sp, #104]
	ldr x9, [x19, #48]
	str x9, [sp, #112]
	ldr x9, [x19, #56]
	str x9, [sp, #120]
	add x0, sp, #64
	ldr x1, [x24, #40]
	add x2, sp, #256
	add x3, x26, #0
	add x4, sp, #336
	ldr x16, [x24, #8]
	blr x16
	add x0, sp, #64
	ldr x1, [x24, #40]
	add x1, x1, x26
	add x2, x20, #0
	add x3, x21, #0
	add x4, sp, #336
	ldr x16, [x24, #8]
	blr x16
	add x2, sp, #320
	strb w25, [x2, #0]
	add x0, sp, #64
	ldr x1, [x24, #40]
	add x1, x1, x26
	add x1, x1, x21
	movz x3, #1, lsl #0
	add x4, sp, #336
	ldr x16, [x24, #8]
	blr x16
	add x0, sp, #64
	add x1, x19, #192
	ldr x2, [x24, #40]
	add x2, x2, x26
	add x2, x2, x21
	add x2, x2, #1
	add x3, sp, #256
	add x4, sp, #336
	ldr x16, [x24, #16]
	blr x16
	ldr x14, [x24, #32]
	subs x9, x23, x14
	csel x14, x14, x23, hs
	add x13, x14, #0
	add x11, sp, #256
	add x12, x22, #0
23:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 23b
	add x22, x22, x14
	sub x23, x23, x14
	ldr x26, [x24, #32]
	add x25, x25, #1
	cbnz x23, 22b
21:
	add x9, sp, #0
	ldr x19, [x9, #0]
	ldr x20, [x9, #8]
	ldr x21, [x9, #16]
	ldr x22, [x9, #24]
	ldr x23, [x9, #32]
	ldr x24, [x9, #40]
	ldr x25, [x9, #48]
	ldr x26, [x9, #56]
	add sp, sp, #2208
	ldr x30, [sp], #16
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
	sub sp, sp, #2240
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #35, lsl #0
24:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 24b
	add sp, sp, #2240
	ret
	.p2align 6
