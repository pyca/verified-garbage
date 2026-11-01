// The functions of `src/ed25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key_expanded:
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
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #32
	ldr x2, [sp, #272]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
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
	ret
	.p2align 6

vg_ed25519_sign_expanded_sha3:
	.arch_extension sha3
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
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #32
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
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
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
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
	ret
	.arch_extension nosha3
	.p2align 6

vg_ed25519_verify_sha3:
	.arch_extension sha3
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
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #264]
	add x2, x2, #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	ldr x1, [sp, #272]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #288]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
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
	ret
	.arch_extension nosha3
	.p2align 6
