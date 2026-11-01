// The functions of `src/ecdsa_p224_sha224.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p224_sha224_sign:
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
	add x13, x1, #4
	add x14, x15, #4
	ldr x8, [x13, #16]
	rev x8, x8
	str x8, [x15, #64]
	movz x12, #10813, lsl #0
	movk x12, #23644, lsl #16
	movk x12, #10565, lsl #32
	movk x12, #5085, lsl #48
	subs x2, x8, x12
	str x2, [x15, #0]
	ldr x8, [x13, #8]
	rev x8, x8
	str x8, [x15, #72]
	movz x12, #61502, lsl #0
	movk x12, #57528, lsl #16
	movk x12, #5794, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #8]
	ldr x8, [x13, #0]
	rev x8, x8
	str x8, [x15, #80]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #16]
	ldr w8, [x1, #0]
	rev w8, w8
	str x8, [x15, #88]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #24]
	sbc x6, x7, x7
	ldr x8, [x15, #64]
	ldr x2, [x15, #0]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #144]
	ldr x8, [x15, #72]
	ldr x2, [x15, #8]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #136]
	ldr x8, [x15, #80]
	ldr x2, [x15, #16]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #128]
	ldr x8, [x15, #88]
	ldr x2, [x15, #24]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #120]
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
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #0, lsl #0
	strb w11, [x9, #2284]
	add x12, x9, #2285
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	add x13, x10, #20
	add x14, x12, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #128
	add x14, x12, #28
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #85, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #149, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #1, lsl #0
	strb w11, [x9, #2284]
	add x12, x9, #2285
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	add x13, x10, #20
	add x14, x12, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #128
	add x14, x12, #28
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #85, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #149, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	ldr x2, [sp, #192]
	add x3, sp, #64
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p224_sign}
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
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #0, lsl #0
	strb w11, [x9, #2284]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #29, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #93, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch}
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

vg_ecdsa_p224_sha224_sign_sha2:
	.arch_extension sha2
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
	add x13, x1, #4
	add x14, x15, #4
	ldr x8, [x13, #16]
	rev x8, x8
	str x8, [x15, #64]
	movz x12, #10813, lsl #0
	movk x12, #23644, lsl #16
	movk x12, #10565, lsl #32
	movk x12, #5085, lsl #48
	subs x2, x8, x12
	str x2, [x15, #0]
	ldr x8, [x13, #8]
	rev x8, x8
	str x8, [x15, #72]
	movz x12, #61502, lsl #0
	movk x12, #57528, lsl #16
	movk x12, #5794, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #8]
	ldr x8, [x13, #0]
	rev x8, x8
	str x8, [x15, #80]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #16]
	ldr w8, [x1, #0]
	rev w8, w8
	str x8, [x15, #88]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #24]
	sbc x6, x7, x7
	ldr x8, [x15, #64]
	ldr x2, [x15, #0]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #144]
	ldr x8, [x15, #72]
	ldr x2, [x15, #8]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #136]
	ldr x8, [x15, #80]
	ldr x2, [x15, #16]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #128]
	ldr x8, [x15, #88]
	ldr x2, [x15, #24]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x14, #120]
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
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #0, lsl #0
	strb w11, [x9, #2284]
	add x12, x9, #2285
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	add x13, x10, #20
	add x14, x12, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #128
	add x14, x12, #28
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #85, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #149, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #1, lsl #0
	strb w11, [x9, #2284]
	add x12, x9, #2285
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	add x13, x10, #20
	add x14, x12, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #128
	add x14, x12, #28
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #85, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #149, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	ldr x2, [sp, #192]
	add x3, sp, #64
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p224_sign}
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
	add x13, x15, #64
	add x14, x9, #2256
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	add x13, x13, #20
	add x14, x14, #20
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	movz x11, #0, lsl #0
	strb w11, [x9, #2284]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #29, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #93, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	add x2, sp, #64
	movz x3, #28, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #92, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha224_finalize_scratch_sha2}
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
	.arch_extension nosha2
	.p2align 6
