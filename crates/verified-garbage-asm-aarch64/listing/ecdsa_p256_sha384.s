// The functions of `src/ecdsa_p256_sha384.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sha384_sign:
	str x30, [sp, #-16]!
	sub sp, sp, #224
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x3, [x15, #184]
	ldr x1, [sp, #192]
	movz x7, #0, lsl #0
	add x15, sp, #0
	ldr x8, [x1, #24]
	rev x8, x8
	str x8, [x15, #64]
	movz x12, #9553, lsl #0
	movk x12, #64611, lsl #16
	movk x12, #51906, lsl #32
	movk x12, #62393, lsl #48
	subs x2, x8, x12
	str x2, [x15, #0]
	ldr x8, [x1, #16]
	rev x8, x8
	str x8, [x15, #72]
	movz x12, #40580, lsl #0
	movk x12, #42775, lsl #16
	movk x12, #64173, lsl #32
	movk x12, #48358, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #8]
	ldr x8, [x1, #8]
	rev x8, x8
	str x8, [x15, #80]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #16]
	ldr x8, [x1, #0]
	rev x8, x8
	str x8, [x15, #88]
	movz x12, #0, lsl #0
	movk x12, #0, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #24]
	sbc x6, x7, x7
	ldr x8, [x15, #64]
	ldr x2, [x15, #0]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #152]
	ldr x8, [x15, #72]
	ldr x2, [x15, #8]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #144]
	ldr x8, [x15, #80]
	ldr x2, [x15, #16]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #136]
	ldr x8, [x15, #88]
	ldr x2, [x15, #24]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #128]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #0, lsl #0
	strb w11, [x9, #2304]
	add x12, x9, #2305
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x15, #128]
	str x11, [x12, #32]
	ldr x11, [x15, #136]
	str x11, [x12, #40]
	ldr x11, [x15, #144]
	str x11, [x12, #48]
	ldr x11, [x15, #152]
	str x11, [x12, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #113, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #241, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #1, lsl #0
	strb w11, [x9, #2304]
	add x12, x9, #2305
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x15, #128]
	str x11, [x12, #32]
	ldr x11, [x15, #136]
	str x11, [x12, #40]
	ldr x11, [x15, #144]
	str x11, [x12, #48]
	ldr x11, [x15, #152]
	str x11, [x12, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #113, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #241, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	ldr x2, [sp, #192]
	add x3, sp, #64
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p256_sign}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 21f
	movz x12, #0, lsl #0
	b 22f
21:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #0, lsl #0
	strb w11, [x9, #2304]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #49, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #177, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch}
	movz x12, #1, lsl #0
22:
	cbnz x12, 20b
	add x15, sp, #0
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
	add sp, sp, #224
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ecdsa_p256_sha384_sign_sha3:
	.arch_extension sha3
	str x30, [sp, #-16]!
	sub sp, sp, #224
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x3, [x15, #184]
	ldr x1, [sp, #192]
	movz x7, #0, lsl #0
	add x15, sp, #0
	ldr x8, [x1, #24]
	rev x8, x8
	str x8, [x15, #64]
	movz x12, #9553, lsl #0
	movk x12, #64611, lsl #16
	movk x12, #51906, lsl #32
	movk x12, #62393, lsl #48
	subs x2, x8, x12
	str x2, [x15, #0]
	ldr x8, [x1, #16]
	rev x8, x8
	str x8, [x15, #72]
	movz x12, #40580, lsl #0
	movk x12, #42775, lsl #16
	movk x12, #64173, lsl #32
	movk x12, #48358, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #8]
	ldr x8, [x1, #8]
	rev x8, x8
	str x8, [x15, #80]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #16]
	ldr x8, [x1, #0]
	rev x8, x8
	str x8, [x15, #88]
	movz x12, #0, lsl #0
	movk x12, #0, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #24]
	sbc x6, x7, x7
	ldr x8, [x15, #64]
	ldr x2, [x15, #0]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #152]
	ldr x8, [x15, #72]
	ldr x2, [x15, #8]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #144]
	ldr x8, [x15, #80]
	ldr x2, [x15, #16]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #136]
	ldr x8, [x15, #88]
	ldr x2, [x15, #24]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #128]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #0, lsl #0
	strb w11, [x9, #2304]
	add x12, x9, #2305
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x15, #128]
	str x11, [x12, #32]
	ldr x11, [x15, #136]
	str x11, [x12, #40]
	ldr x11, [x15, #144]
	str x11, [x12, #48]
	ldr x11, [x15, #152]
	str x11, [x12, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #113, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #241, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #1, lsl #0
	strb w11, [x9, #2304]
	add x12, x9, #2305
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x15, #128]
	str x11, [x12, #32]
	ldr x11, [x15, #136]
	str x11, [x12, #40]
	ldr x11, [x15, #144]
	str x11, [x12, #48]
	ldr x11, [x15, #152]
	str x11, [x12, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #113, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #241, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	ldr x2, [sp, #192]
	add x3, sp, #64
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p256_sign}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 21f
	movz x12, #0, lsl #0
	b 22f
21:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	movz x11, #0, lsl #0
	strb w11, [x9, #2304]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #49, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #177, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #48, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #176, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha384_finalize_scratch_sha3}
	movz x12, #1, lsl #0
22:
	cbnz x12, 20b
	add x15, sp, #0
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
	add sp, sp, #224
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6
