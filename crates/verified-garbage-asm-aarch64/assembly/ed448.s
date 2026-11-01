// The functions of `src/ed448.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
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
	ldr x15, [sp, #272]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #272]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #57, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #272]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch}
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #128
	movz x4, #114, lsl #0
	ldr x5, [sp, #272]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch}
	ldr x9, [sp, #128]
	movz x10, #65532, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #136]
	add x15, sp, #8
	str x9, [x15, #0]
	ldr x9, [sp, #144]
	add x15, sp, #16
	str x9, [x15, #0]
	ldr x9, [sp, #152]
	add x15, sp, #24
	str x9, [x15, #0]
	ldr x9, [sp, #160]
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #168]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #176]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	add x15, sp, #48
	str x9, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	bl {vg_ed448_scalar_base}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #8]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #16]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #24]
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

vg_ed448_sign_cached:
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
	add x15, sp, #200
	str x6, [x15, #0]
	add x15, sp, #208
	str x7, [x15, #0]
	movz x9, #26963, lsl #0
	movk x9, #17767, lsl #16
	movk x9, #13412, lsl #32
	movk x9, #14388, lsl #48
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #288]
	add x9, x9, #0
	lsl x9, x9, #8
	str x9, [x15, #8]
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch}
	ldr x9, [sp, #16]
	movz x10, #65532, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #136
	str x9, [x15, #0]
	ldr x9, [sp, #24]
	add x15, sp, #144
	str x9, [x15, #0]
	ldr x9, [sp, #32]
	add x15, sp, #152
	str x9, [x15, #0]
	ldr x9, [sp, #40]
	add x15, sp, #160
	str x9, [x15, #0]
	ldr x9, [sp, #48]
	add x15, sp, #168
	str x9, [x15, #0]
	ldr x9, [sp, #56]
	add x15, sp, #176
	str x9, [x15, #0]
	ldr x9, [sp, #64]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	add x15, sp, #184
	str x9, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #73
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	ldr x4, [sp, #200]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch}
	ldr x0, [sp, #256]
	add x0, x0, #57
	add x1, sp, #16
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #256]
	add x1, x1, #57
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_base}
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #256]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	ldr x4, [sp, #200]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch}
	add x0, sp, #16
	add x1, sp, #16
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #57
	ldr x1, [sp, #256]
	add x1, x1, #57
	add x2, sp, #16
	add x3, sp, #136
	ldr x4, [sp, #208]
	add x4, x4, #0
	bl {vg_ed448_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #16]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #24]
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
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ed448_verify:
	lsr x9, x2, #8
	cbz x9, 20f
	movz x0, #0, lsl #0
	b 21f
20:
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
	add x15, sp, #248
	str x6, [x15, #0]
	movz x9, #26963, lsl #0
	movk x9, #17767, lsl #16
	movk x9, #13412, lsl #32
	movk x9, #14388, lsl #48
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #272]
	add x9, x9, #0
	lsl x9, x9, #8
	str x9, [x15, #8]
	ldr x15, [sp, #248]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	ldr x4, [sp, #272]
	add x4, x4, #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #256]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #248]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch}
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch}
	add x0, sp, #136
	add x1, sp, #16
	ldr x2, [sp, #248]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #296]
	add x1, x1, #0
	add x2, sp, #136
	ldr x3, [sp, #248]
	add x3, x3, #0
	bl {vg_ed448_verify_equation}
	add sp, sp, #320
	ldr x30, [sp], #16
21:
	ret
	.p2align 6

vg_ed448_public_key_sha3:
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
	ldr x15, [sp, #272]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #272]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #57, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #272]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch_sha3}
	ldr x0, [sp, #272]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #128
	movz x4, #114, lsl #0
	ldr x5, [sp, #272]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x9, [sp, #128]
	movz x10, #65532, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #136]
	add x15, sp, #8
	str x9, [x15, #0]
	ldr x9, [sp, #144]
	add x15, sp, #16
	str x9, [x15, #0]
	ldr x9, [sp, #152]
	add x15, sp, #24
	str x9, [x15, #0]
	ldr x9, [sp, #160]
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #168]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #176]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	add x15, sp, #48
	str x9, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	bl {vg_ed448_scalar_base}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #8]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #16]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #24]
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

vg_ed448_sign_cached_sha3:
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
	add x15, sp, #200
	str x6, [x15, #0]
	add x15, sp, #208
	str x7, [x15, #0]
	movz x9, #26963, lsl #0
	movk x9, #17767, lsl #16
	movk x9, #13412, lsl #32
	movk x9, #14388, lsl #48
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #288]
	add x9, x9, #0
	lsl x9, x9, #8
	str x9, [x15, #8]
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch_sha3}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x9, [sp, #16]
	movz x10, #65532, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #136
	str x9, [x15, #0]
	ldr x9, [sp, #24]
	add x15, sp, #144
	str x9, [x15, #0]
	ldr x9, [sp, #32]
	add x15, sp, #152
	str x9, [x15, #0]
	ldr x9, [sp, #40]
	add x15, sp, #160
	str x9, [x15, #0]
	ldr x9, [sp, #48]
	add x15, sp, #168
	str x9, [x15, #0]
	ldr x9, [sp, #56]
	add x15, sp, #176
	str x9, [x15, #0]
	ldr x9, [sp, #64]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	add x15, sp, #184
	str x9, [x15, #0]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #73
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	ldr x4, [sp, #200]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch_sha3}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x0, [sp, #256]
	add x0, x0, #57
	add x1, sp, #16
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #256]
	add x1, x1, #57
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_base}
	ldr x15, [sp, #208]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #256]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	ldr x4, [sp, #200]
	add x4, x4, #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #208]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch_sha3}
	ldr x0, [sp, #208]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #208]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch_sha3}
	add x0, sp, #16
	add x1, sp, #16
	ldr x2, [sp, #208]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #57
	ldr x1, [sp, #256]
	add x1, x1, #57
	add x2, sp, #16
	add x3, sp, #136
	ldr x4, [sp, #208]
	add x4, x4, #0
	bl {vg_ed448_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #16]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #24]
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
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6

vg_ed448_verify_sha3:
	.arch_extension sha3
	lsr x9, x2, #8
	cbz x9, 20f
	movz x0, #0, lsl #0
	b 21f
20:
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
	add x15, sp, #248
	str x6, [x15, #0]
	movz x9, #26963, lsl #0
	movk x9, #17767, lsl #16
	movk x9, #13412, lsl #32
	movk x9, #14388, lsl #48
	add x15, sp, #0
	str x9, [x15, #0]
	ldr x9, [sp, #272]
	add x9, x9, #0
	lsl x9, x9, #8
	str x9, [x15, #8]
	ldr x15, [sp, #248]
	add x15, x15, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #176]
	str x14, [x15, #184]
	str x14, [x15, #192]
	movz x2, #0, lsl #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	add x3, sp, #0
	movz x4, #10, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #264]
	add x3, x3, #0
	ldr x4, [sp, #272]
	add x4, x4, #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #296]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #256]
	add x3, x3, #0
	movz x4, #57, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	ldr x3, [sp, #280]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	ldr x4, [sp, #248]
	add x4, x4, #256
	bl {vg_keccak_pad_scratch_sha3}
	ldr x0, [sp, #248]
	add x0, x0, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, sp, #16
	movz x4, #114, lsl #0
	ldr x5, [sp, #248]
	add x5, x5, #256
	bl {vg_keccak_squeeze_scratch_sha3}
	add x0, sp, #136
	add x1, sp, #16
	ldr x2, [sp, #248]
	add x2, x2, #0
	bl {vg_ed448_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #296]
	add x1, x1, #0
	add x2, sp, #136
	ldr x3, [sp, #248]
	add x3, x3, #0
	bl {vg_ed448_verify_equation}
	add sp, sp, #320
	ldr x30, [sp], #16
21:
	ret
	.arch_extension nosha3
	.p2align 6
