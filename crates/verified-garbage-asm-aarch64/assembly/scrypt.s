// The functions of `src/scrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_sha2:
	str x30, [sp, #-16]!
	sub sp, sp, #64
	add x15, sp, #0
	str x0, [x15, #8]
	str x1, [x15, #16]
	str x4, [x15, #24]
	str x5, [x15, #32]
	str x6, [x15, #40]
	str x7, [x15, #48]
	movz x4, #1, lsl #0
	lsl x6, x6, #7
	ldr x7, [sp, #88]
	bl {vg_pbkdf2_hmac_sha256_scratch_sha2}
	ldr x9, [sp, #32]
	add x15, sp, #0
	str x9, [x15, #0]
20:
	ldr x0, [sp, #0]
	ldr x1, [sp, #24]
	ldr x2, [sp, #48]
	ldr x3, [sp, #80]
	ldr x4, [sp, #88]
	add x5, x1, #2
	bl {vg_scrypt_romix}
	ldr x9, [sp, #0]
	ldr x10, [sp, #24]
	lsl x10, x10, #7
	add x9, x9, x10
	ldr x11, [sp, #32]
	ldr x12, [sp, #40]
	lsl x12, x12, #7
	add x11, x11, x12
	sub x11, x11, x9
	add x15, sp, #0
	str x9, [x15, #0]
	cbnz x11, 20b
	ldr x0, [sp, #8]
	ldr x1, [sp, #16]
	ldr x2, [sp, #32]
	ldr x3, [sp, #40]
	lsl x3, x3, #7
	movz x4, #1, lsl #0
	ldr x5, [sp, #104]
	ldr x6, [sp, #112]
	ldr x7, [sp, #88]
	bl {vg_pbkdf2_hmac_sha256_scratch_sha2}
	add sp, sp, #64
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #96
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	add sp, sp, #96
	ret
	.p2align 6

vg_scrypt:
	str x30, [sp, #-16]!
	sub sp, sp, #64
	add x15, sp, #0
	str x0, [x15, #8]
	str x1, [x15, #16]
	str x4, [x15, #24]
	str x5, [x15, #32]
	str x6, [x15, #40]
	str x7, [x15, #48]
	movz x4, #1, lsl #0
	lsl x6, x6, #7
	ldr x7, [sp, #88]
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ldr x9, [sp, #32]
	add x15, sp, #0
	str x9, [x15, #0]
20:
	ldr x0, [sp, #0]
	ldr x1, [sp, #24]
	ldr x2, [sp, #48]
	ldr x3, [sp, #80]
	ldr x4, [sp, #88]
	add x5, x1, #2
	bl {vg_scrypt_romix}
	ldr x9, [sp, #0]
	ldr x10, [sp, #24]
	lsl x10, x10, #7
	add x9, x9, x10
	ldr x11, [sp, #32]
	ldr x12, [sp, #40]
	lsl x12, x12, #7
	add x11, x11, x12
	sub x11, x11, x9
	add x15, sp, #0
	str x9, [x15, #0]
	cbnz x11, 20b
	ldr x0, [sp, #8]
	ldr x1, [sp, #16]
	ldr x2, [sp, #32]
	ldr x3, [sp, #40]
	lsl x3, x3, #7
	movz x4, #1, lsl #0
	ldr x5, [sp, #104]
	ldr x6, [sp, #112]
	ldr x7, [sp, #88]
	bl {vg_pbkdf2_hmac_sha256_scratch}
	add sp, sp, #64
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #96
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	add sp, sp, #96
	ret
	.p2align 6
