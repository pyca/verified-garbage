// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_gcm_seal_ctr32_sm4_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_seal_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1024
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #16, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	add sp, sp, #1024
	ret
	.p2align 6

vg_sm4_gcm_open_ctr32_sm4_ghash_aes:
	sub sp, sp, #32
	add x16, sp, #0
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	str x30, [sp, #16]
	umov x16, v8.d[0]
	str x16, [sp, #24]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_open_core_ctr32_sm4}
	ldr x16, [sp, #24]
	mov v8.d[0], x16
	ldr x30, [sp, #16]
	add sp, sp, #32
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
	add w0, w0, #0
	sub sp, sp, #1040
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #16, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #1040
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt_ctr32_sm4_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_encrypt_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt_ctr32_sm4_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_decrypt_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_finish_ctr32_sm4_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_finish_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_verify_ctr32_sm4_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_verify_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	add w0, w0, #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_init_ctr32_sm4:
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
	bl {vg_sm4_expand_key_sm4}
	movz x9, #0, lsl #0
	str x9, [x21, #240]
	str x9, [x21, #248]
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x19, #96
	add x2, x21, #240
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32_sm4}
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
	sub sp, sp, #992
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #992
	ret
	.p2align 6

vg_sm4_gcm_seal_ctr32_sm4:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_seal_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1024
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #16, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	add sp, sp, #1024
	ret
	.p2align 6

vg_sm4_gcm_open_ctr32_sm4:
	sub sp, sp, #32
	add x16, sp, #0
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	str x30, [sp, #16]
	umov x16, v8.d[0]
	str x16, [sp, #24]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_open_core_ctr32_sm4}
	ldr x16, [sp, #24]
	mov v8.d[0], x16
	ldr x30, [sp, #16]
	add sp, sp, #32
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
	add w0, w0, #0
	sub sp, sp, #1040
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #16, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #1040
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt_ctr32_sm4:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_encrypt_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt_ctr32_sm4:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_decrypt_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_finish_ctr32_sm4:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_finish_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_stream_verify_ctr32_sm4:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_verify_core_ctr32_sm4}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	add w0, w0, #0
	sub sp, sp, #1008
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #15, lsl #0
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
	add sp, sp, #1008
	ret
	.p2align 6

vg_sm4_gcm_seal_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_seal_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4064
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
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
	add sp, sp, #4064
	ret
	.p2align 6

vg_sm4_gcm_open_ghash_aes:
	sub sp, sp, #32
	add x16, sp, #0
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	str x30, [sp, #16]
	umov x16, v8.d[0]
	str x16, [sp, #24]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_open_core}
	ldr x16, [sp, #24]
	mov v8.d[0], x16
	ldr x30, [sp, #16]
	add sp, sp, #32
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
	add w0, w0, #0
	sub sp, sp, #4080
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
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
	add sp, sp, #4080
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_encrypt_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_decrypt_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_finish_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_finish_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_verify_ghash_aes:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_aes}
	add x16, x16, {vg_ghash_aes}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_verify_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	add w0, w0, #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_init_aes:
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
	sub sp, sp, #2560
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #40, lsl #0
217:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 217b
	add sp, sp, #2560
	ret
	.p2align 6

vg_sm4_gcm_stream_aad_aes:
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
	sub sp, sp, #2560
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #40, lsl #0
222:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 222b
	add sp, sp, #2560
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
	bl {vg_sm4_expand_key_core}
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
	sub sp, sp, #4032
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	add sp, sp, #4032
	ret
	.p2align 6

vg_sm4_gcm_seal:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_seal_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4064
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
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
	add sp, sp, #4064
	ret
	.p2align 6

vg_sm4_gcm_open:
	sub sp, sp, #32
	add x16, sp, #0
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	str x30, [sp, #16]
	umov x16, v8.d[0]
	str x16, [sp, #24]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_open_core}
	ldr x16, [sp, #24]
	mov v8.d[0], x16
	ldr x30, [sp, #16]
	add sp, sp, #32
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
	add w0, w0, #0
	sub sp, sp, #4080
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
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
	add sp, sp, #4080
	ret
	.p2align 6

vg_sm4_gcm_stream_encrypt:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_encrypt_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_decrypt:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_decrypt_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_finish:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_finish_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	movz x0, #0, lsl #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
	ret
	.p2align 6

vg_sm4_gcm_stream_verify:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_ghash_neon}
	add x16, x16, {vg_ghash_neon}
	mov v8.d[0], x16
	bl {vg_sm4_gcm_stream_verify_core}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
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
	add w0, w0, #0
	sub sp, sp, #4048
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #63, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #4048
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
	bl {vg_ghash_neon}
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
	bl {vg_ghash_neon}
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
	bl {vg_ghash_neon}
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
	sub sp, sp, #2560
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #40, lsl #0
217:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 217b
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
	bl {vg_ghash_neon}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_neon}
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
	sub sp, sp, #2560
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #40, lsl #0
222:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 222b
	add sp, sp, #2560
	ret
	.p2align 6
