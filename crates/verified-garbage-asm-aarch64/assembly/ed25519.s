// The functions of `src/ed25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_key_pair_sha512:
	str x30, [sp, #-16]!
	sub sp, sp, #32
	str x0, [sp, #0]
	str x1, [sp, #8]
	str x3, [sp, #16]
	add x0, x2, #0
	add x2, x1, #0
	movz x1, #32, lsl #0
	bl {vg_sha512_digest_sha512}
	ldr x0, [sp, #0]
	ldr x1, [sp, #8]
	ldr x2, [sp, #16]
	bl {vg_ed25519_public_key_expanded}
	add sp, sp, #32
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
	sub sp, sp, #944
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	add sp, sp, #944
	ret
	.p2align 6

vg_ed25519_key_pair:
	str x30, [sp, #-16]!
	sub sp, sp, #32
	str x0, [sp, #0]
	str x1, [sp, #8]
	str x3, [sp, #16]
	add x0, x2, #0
	add x2, x1, #0
	movz x1, #32, lsl #0
	bl {vg_sha512_digest}
	ldr x0, [sp, #0]
	ldr x1, [sp, #8]
	ldr x2, [sp, #16]
	bl {vg_ed25519_public_key_expanded}
	add sp, sp, #32
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
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #944
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	add sp, sp, #944
	ret
	.p2align 6

vg_ed25519_sign_expanded_sha512:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x1, [sp, #264]
	add x1, x1, #0
	add x15, sp, #192
	ldr x9, [x1, #0]
	str x9, [x15, #0]
	ldr x9, [x1, #8]
	str x9, [x15, #8]
	ldr x9, [x1, #16]
	str x9, [x15, #16]
	ldr x9, [x1, #24]
	str x9, [x15, #24]
	ldr x9, [x1, #32]
	str x9, [x15, #32]
	ldr x9, [x1, #40]
	str x9, [x15, #40]
	ldr x9, [x1, #48]
	str x9, [x15, #48]
	ldr x9, [x1, #56]
	str x9, [x15, #56]
	ldr x9, [sp, #192]
	movz x10, #65528, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #200]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #208]
	add x15, sp, #48
	str x9, [x15, #0]
	ldr x9, [sp, #216]
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #16383, lsl #48
	and x9, x9, x10
	movz x10, #16384, lsl #48
	orr x9, x9, x10
	add x15, sp, #56
	str x9, [x15, #0]
	ldr x0, [sp, #224]
	add x15, sp, #64
	str x0, [x15, #0]
	ldr x0, [sp, #232]
	add x15, sp, #64
	str x0, [x15, #8]
	ldr x0, [sp, #240]
	add x15, sp, #64
	str x0, [x15, #16]
	ldr x0, [sp, #248]
	add x15, sp, #64
	str x0, [x15, #24]
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	add x2, sp, #64
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #32
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha512}
	add x0, sp, #96
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #96
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha512}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #32
	add x1, sp, #96
	add x2, sp, #128
	add x3, sp, #32
	ldr x4, [sp, #296]
	add x4, x4, #0
	bl {vg_ed25519_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #32]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #40]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #48]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #64]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #72]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #80]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #88]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #96]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #104]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #112]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #120]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #128]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #136]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #144]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #152]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #200]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #208]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #216]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #224]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #232]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #240]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #248]
	add sp, sp, #320
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
	sub sp, sp, #352
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	add sp, sp, #352
	ret
	.p2align 6

vg_ed25519_sign_expanded:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x1, [sp, #264]
	add x1, x1, #0
	add x15, sp, #192
	ldr x9, [x1, #0]
	str x9, [x15, #0]
	ldr x9, [x1, #8]
	str x9, [x15, #8]
	ldr x9, [x1, #16]
	str x9, [x15, #16]
	ldr x9, [x1, #24]
	str x9, [x15, #24]
	ldr x9, [x1, #32]
	str x9, [x15, #32]
	ldr x9, [x1, #40]
	str x9, [x15, #40]
	ldr x9, [x1, #48]
	str x9, [x15, #48]
	ldr x9, [x1, #56]
	str x9, [x15, #56]
	ldr x9, [sp, #192]
	movz x10, #65528, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #200]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #208]
	add x15, sp, #48
	str x9, [x15, #0]
	ldr x9, [sp, #216]
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #16383, lsl #48
	and x9, x9, x10
	movz x10, #16384, lsl #48
	orr x9, x9, x10
	add x15, sp, #56
	str x9, [x15, #0]
	ldr x0, [sp, #224]
	add x15, sp, #64
	str x0, [x15, #0]
	ldr x0, [sp, #232]
	add x15, sp, #64
	str x0, [x15, #8]
	ldr x0, [sp, #240]
	add x15, sp, #64
	str x0, [x15, #16]
	ldr x0, [sp, #248]
	add x15, sp, #64
	str x0, [x15, #24]
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	add x2, sp, #64
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #32
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #96
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #96
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #32
	add x1, sp, #96
	add x2, sp, #128
	add x3, sp, #32
	ldr x4, [sp, #296]
	add x4, x4, #0
	bl {vg_ed25519_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #32]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #40]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #48]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #64]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #72]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #80]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #88]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #96]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #104]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #112]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #120]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #128]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #136]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #144]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #152]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #200]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #208]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #216]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #224]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #232]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #240]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #248]
	add sp, sp, #320
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
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #352
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	add sp, sp, #352
	ret
	.p2align 6

vg_ed25519_verify_sha512:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x0, [sp, #288]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #264]
	add x2, x2, #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha512}
	ldr x0, [sp, #288]
	add x0, x0, #0
	ldr x1, [sp, #272]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #288]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha512}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #288]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #280]
	add x1, x1, #0
	add x2, sp, #128
	ldr x3, [sp, #288]
	add x3, x3, #0
	bl {vg_ed25519_verify_equation}
	add sp, sp, #320
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
	add w0, w0, #0
	sub sp, sp, #352
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	add sp, sp, #352
	ret
	.p2align 6

vg_ed25519_verify:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x0, [sp, #288]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #264]
	add x2, x2, #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	ldr x1, [sp, #272]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #288]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #288]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #280]
	add x1, x1, #0
	add x2, sp, #128
	ldr x3, [sp, #288]
	add x3, x3, #0
	bl {vg_ed25519_verify_equation}
	add sp, sp, #320
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
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #352
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	add sp, sp, #352
	ret
	.p2align 6
