// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt:
	str x30, [sp, #-16]!
	sub sp, sp, #208
	add x9, sp, #0
	str x0, [x9, #96]
	str x2, [x9, #104]
	str x3, [x9, #112]
	str x4, [x9, #120]
	str x5, [x9, #128]
	str x6, [x9, #136]
	str x7, [x9, #144]
	ldr x10, [sp, #224]
	str x10, [x9, #152]
	ldr x10, [sp, #232]
	str x10, [x9, #160]
	ldr x10, [sp, #328]
	str x10, [x9, #168]
	ldr x10, [sp, #248]
	str x10, [x9, #0]
	ldr x10, [sp, #256]
	str x10, [x9, #8]
	ldr x10, [sp, #264]
	str x10, [x9, #16]
	ldr x10, [sp, #272]
	str x10, [x9, #24]
	ldr x10, [sp, #280]
	str x10, [x9, #32]
	ldr x10, [sp, #288]
	str x10, [x9, #40]
	ldr x10, [sp, #296]
	str x10, [x9, #48]
	ldr x10, [sp, #304]
	str x10, [x9, #56]
	ldr x10, [sp, #312]
	str x10, [x9, #64]
	ldr x10, [sp, #320]
	str x10, [x9, #72]
	ldr x10, [sp, #328]
	str x10, [x9, #80]
	ldr x10, [sp, #336]
	str x10, [x9, #88]
	orr x1, x4, x4
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	ldr x6, [sp, #232]
	orr x7, x1, x1
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #176]
	ldr x11, [sp, #168]
	add x11, x11, #2416
	ldr x12, [sp, #120]
	movz x13, #0, lsl #0
20:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x14, [sp, #144]
	ldr x12, [sp, #152]
	ldr x11, [sp, #168]
	add x11, x11, #2416
	ldr x15, [sp, #120]
	add x11, x11, x15
	sub x11, x11, x12
21:
	ldrb w10, [x14, #0]
	strb w10, [x11, #0]
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 21b
	ldr x0, [sp, #168]
	add x0, x0, #0
	bl {vg_sha256_init}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #2416
	ldr x3, [sp, #120]
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #120]
	ldr x2, [sp, #168]
	add x2, x2, #1040
	ldr x3, [sp, #168]
	add x3, x3, #192
	bl {vg_sha256_finalize_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1040
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #160]
	ldr x3, [sp, #120]
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #120]
	add x2, x2, #64
	ldr x3, [sp, #168]
	add x3, x3, #1104
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #184]
	ldr x10, [sp, #120]
	add x10, x10, #31
	lsr x10, x10, #5
	str x10, [x9, #192]
22:
	ldr x9, [sp, #168]
	add x9, x9, #1024
	ldr x11, [sp, #184]
	ldr x12, [sp, #120]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #108, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #110, lsl #0
	strb w10, [x9, #4]
	movz x10, #103, lsl #0
	strb w10, [x9, #5]
	movz x10, #116, lsl #0
	strb w10, [x9, #6]
	movz x10, #104, lsl #0
	strb w10, [x9, #7]
	movz x10, #8, lsl #0
	strb w10, [x9, #8]
	movz x10, #0, lsl #0
	strb w10, [x9, #9]
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #1024
	movz x3, #10, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	movz x2, #74, lsl #0
	ldr x3, [sp, #184]
	lsl x3, x3, #5
	ldr x10, [sp, #168]
	add x10, x10, #1136
	add x3, x3, x10
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	ldr x11, [sp, #184]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #184]
	movz x12, #8, lsl #0
	sub x12, x12, x11
	cbnz x12, 22b
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #184]
23:
	ldr x9, [sp, #168]
	add x9, x9, #1024
	ldr x11, [sp, #184]
	ldr x12, [sp, #120]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #109, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #115, lsl #0
	strb w10, [x9, #4]
	movz x10, #115, lsl #0
	strb w10, [x9, #5]
	movz x10, #97, lsl #0
	strb w10, [x9, #6]
	movz x10, #103, lsl #0
	strb w10, [x9, #7]
	movz x10, #101, lsl #0
	strb w10, [x9, #8]
	lsl x10, x12, #3
	strb w10, [x9, #10]
	lsr x10, x10, #8
	strb w10, [x9, #9]
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #1024
	movz x3, #11, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	movz x2, #75, lsl #0
	ldr x3, [sp, #184]
	lsl x3, x3, #5
	ldr x10, [sp, #168]
	add x10, x10, #1392
	add x3, x3, x10
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	ldr x11, [sp, #184]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #184]
	ldr x12, [sp, #192]
	sub x12, x12, x11
	cbnz x12, 23b
	ldr x9, [sp, #120]
	sub x9, x9, #11
	movz x8, #0, lsl #0
24:
	add x8, x8, x8
	add x8, x8, #1
	subs x10, x8, x9
	sbc x10, x10, x10
	cbnz x10, 24b
	ldr x11, [sp, #168]
	add x11, x11, #1136
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
25:
	ldrb w10, [x11, #0]
	lsl x10, x10, #8
	ldrb w14, [x11, #1]
	add x10, x10, x14
	and x10, x10, x8
	subs x14, x9, x10
	csel x13, x10, x13, hs
	add x11, x11, #2
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #96]
	add x11, x11, #2
	ldr x12, [sp, #120]
	sub x12, x12, #2
	movz x14, #2, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #1, lsl #0
26:
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	bic x9, x10, x15, ror #0
	and x9, x9, x14
	orr x16, x16, x9
	orr x15, x15, x10
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 26b
	ldr x11, [sp, #96]
	ldr x12, [sp, #120]
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	ldrb w9, [x11, #1]
	movz x14, #2, lsl #0
	eor x9, x9, x14
	subs x9, x9, x17
	sbc x9, x9, x9
	and x10, x10, x9
	and x15, x15, x10
	movz x14, #10, lsl #0
	subs x9, x16, x14
	sbc x9, x9, x9
	bic x15, x15, x9, ror #0
	sub x9, x12, x16
	sub x9, x9, #1
	eor x9, x9, x13
	and x9, x9, x15
	eor x13, x13, x9
	ldr x14, [sp, #176]
	eor x14, x14, x17
	subs x14, x14, x17
	sbc x14, x14, x14
	sub x16, x12, x13
	and x13, x13, x14
	ldr x10, [sp, #104]
	str x13, [x10, #0]
	ldr x10, [sp, #168]
	add x10, x10, #1392
	movz x9, #0, lsl #0
27:
	ldrb w13, [x11, #0]
	ldrb w8, [x10, #0]
	eor x13, x13, x8
	and x13, x13, x15
	eor x13, x13, x8
	subs x8, x9, x16
	sbc x8, x8, x8
	bic x8, x14, x8, ror #0
	and x13, x13, x8
	strb w13, [x11, #0]
	add x9, x9, #1
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 27b
	ldr x0, [sp, #176]
	add sp, sp, #208
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #208
	add x9, sp, #0
	str x0, [x9, #96]
	str x2, [x9, #104]
	str x3, [x9, #112]
	str x4, [x9, #120]
	str x5, [x9, #128]
	str x6, [x9, #136]
	str x7, [x9, #144]
	ldr x10, [sp, #224]
	str x10, [x9, #152]
	ldr x10, [sp, #232]
	str x10, [x9, #160]
	ldr x10, [sp, #328]
	str x10, [x9, #168]
	ldr x10, [sp, #248]
	str x10, [x9, #0]
	ldr x10, [sp, #256]
	str x10, [x9, #8]
	ldr x10, [sp, #264]
	str x10, [x9, #16]
	ldr x10, [sp, #272]
	str x10, [x9, #24]
	ldr x10, [sp, #280]
	str x10, [x9, #32]
	ldr x10, [sp, #288]
	str x10, [x9, #40]
	ldr x10, [sp, #296]
	str x10, [x9, #48]
	ldr x10, [sp, #304]
	str x10, [x9, #56]
	ldr x10, [sp, #312]
	str x10, [x9, #64]
	ldr x10, [sp, #320]
	str x10, [x9, #72]
	ldr x10, [sp, #328]
	str x10, [x9, #80]
	ldr x10, [sp, #336]
	str x10, [x9, #88]
	orr x1, x4, x4
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	ldr x6, [sp, #232]
	orr x7, x1, x1
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #176]
	ldr x11, [sp, #168]
	add x11, x11, #2416
	ldr x12, [sp, #120]
	movz x13, #0, lsl #0
20:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x14, [sp, #144]
	ldr x12, [sp, #152]
	ldr x11, [sp, #168]
	add x11, x11, #2416
	ldr x15, [sp, #120]
	add x11, x11, x15
	sub x11, x11, x12
21:
	ldrb w10, [x14, #0]
	strb w10, [x11, #0]
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 21b
	ldr x0, [sp, #168]
	add x0, x0, #0
	bl {vg_sha256_init}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #2416
	ldr x3, [sp, #120]
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #120]
	ldr x2, [sp, #168]
	add x2, x2, #1040
	ldr x3, [sp, #168]
	add x3, x3, #192
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1040
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #160]
	ldr x3, [sp, #120]
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #120]
	add x2, x2, #64
	ldr x3, [sp, #168]
	add x3, x3, #1104
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #184]
	ldr x10, [sp, #120]
	add x10, x10, #31
	lsr x10, x10, #5
	str x10, [x9, #192]
22:
	ldr x9, [sp, #168]
	add x9, x9, #1024
	ldr x11, [sp, #184]
	ldr x12, [sp, #120]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #108, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #110, lsl #0
	strb w10, [x9, #4]
	movz x10, #103, lsl #0
	strb w10, [x9, #5]
	movz x10, #116, lsl #0
	strb w10, [x9, #6]
	movz x10, #104, lsl #0
	strb w10, [x9, #7]
	movz x10, #8, lsl #0
	strb w10, [x9, #8]
	movz x10, #0, lsl #0
	strb w10, [x9, #9]
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #1024
	movz x3, #10, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	movz x2, #74, lsl #0
	ldr x3, [sp, #184]
	lsl x3, x3, #5
	ldr x10, [sp, #168]
	add x10, x10, #1136
	add x3, x3, x10
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #184]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #184]
	movz x12, #8, lsl #0
	sub x12, x12, x11
	cbnz x12, 22b
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #184]
23:
	ldr x9, [sp, #168]
	add x9, x9, #1024
	ldr x11, [sp, #184]
	ldr x12, [sp, #120]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #109, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #115, lsl #0
	strb w10, [x9, #4]
	movz x10, #115, lsl #0
	strb w10, [x9, #5]
	movz x10, #97, lsl #0
	strb w10, [x9, #6]
	movz x10, #103, lsl #0
	strb w10, [x9, #7]
	movz x10, #101, lsl #0
	strb w10, [x9, #8]
	lsl x10, x12, #3
	strb w10, [x9, #10]
	lsr x10, x10, #8
	strb w10, [x9, #9]
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	ldr x2, [sp, #168]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #168]
	add x2, x2, #1024
	movz x3, #11, lsl #0
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #168]
	add x0, x0, #0
	ldr x1, [sp, #168]
	add x1, x1, #96
	movz x2, #75, lsl #0
	ldr x3, [sp, #184]
	lsl x3, x3, #5
	ldr x10, [sp, #168]
	add x10, x10, #1392
	add x3, x3, x10
	ldr x4, [sp, #168]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #184]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #184]
	ldr x12, [sp, #192]
	sub x12, x12, x11
	cbnz x12, 23b
	ldr x9, [sp, #120]
	sub x9, x9, #11
	movz x8, #0, lsl #0
24:
	add x8, x8, x8
	add x8, x8, #1
	subs x10, x8, x9
	sbc x10, x10, x10
	cbnz x10, 24b
	ldr x11, [sp, #168]
	add x11, x11, #1136
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
25:
	ldrb w10, [x11, #0]
	lsl x10, x10, #8
	ldrb w14, [x11, #1]
	add x10, x10, x14
	and x10, x10, x8
	subs x14, x9, x10
	csel x13, x10, x13, hs
	add x11, x11, #2
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #96]
	add x11, x11, #2
	ldr x12, [sp, #120]
	sub x12, x12, #2
	movz x14, #2, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #1, lsl #0
26:
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	bic x9, x10, x15, ror #0
	and x9, x9, x14
	orr x16, x16, x9
	orr x15, x15, x10
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 26b
	ldr x11, [sp, #96]
	ldr x12, [sp, #120]
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	ldrb w9, [x11, #1]
	movz x14, #2, lsl #0
	eor x9, x9, x14
	subs x9, x9, x17
	sbc x9, x9, x9
	and x10, x10, x9
	and x15, x15, x10
	movz x14, #10, lsl #0
	subs x9, x16, x14
	sbc x9, x9, x9
	bic x15, x15, x9, ror #0
	sub x9, x12, x16
	sub x9, x9, #1
	eor x9, x9, x13
	and x9, x9, x15
	eor x13, x13, x9
	ldr x14, [sp, #176]
	eor x14, x14, x17
	subs x14, x14, x17
	sbc x14, x14, x14
	sub x16, x12, x13
	and x13, x13, x14
	ldr x10, [sp, #104]
	str x13, [x10, #0]
	ldr x10, [sp, #168]
	add x10, x10, #1392
	movz x9, #0, lsl #0
27:
	ldrb w13, [x11, #0]
	ldrb w8, [x10, #0]
	eor x13, x13, x8
	and x13, x13, x15
	eor x13, x13, x8
	subs x8, x9, x16
	sbc x8, x8, x8
	bic x8, x14, x8, ror #0
	and x13, x13, x8
	strb w13, [x11, #0]
	add x9, x9, #1
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 27b
	ldr x0, [sp, #176]
	add sp, sp, #208
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_pkcs1_encrypt_precomputed:
	str x30, [sp, #-16]!
	sub sp, sp, #1072
	ldr x10, [sp, #1104]
	ldr x11, [sp, #1112]
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	str x0, [x9, #16]
	str x3, [x9, #24]
	movz x10, #0, lsl #0
	strb w10, [x9, #40]
	movz x10, #2, lsl #0
	strb w10, [x9, #41]
	ldr x11, [sp, #1088]
	ldr x12, [sp, #1096]
	add x13, x9, #42
	movz x14, #0, lsl #0
	movz x15, #1, lsl #0
20:
	ldrb w10, [x11, #0]
	strb w10, [x13, #0]
	subs x16, x10, x15
	sbc x16, x10, x10
	orr x14, x14, x16
	add x11, x11, #1
	add x13, x13, #1
	sub x12, x12, #1
	cbnz x12, 20b
	movz x10, #0, lsl #0
	strb w10, [x13, #0]
	add x13, x13, #1
	add x9, sp, #0
	str x14, [x9, #32]
	cbnz x7, 21f
	b 22f
21:
23:
	ldrb w10, [x6, #0]
	strb w10, [x13, #0]
	add x6, x6, #1
	add x13, x13, #1
	sub x7, x7, #1
	cbnz x7, 23b
22:
	add x6, sp, #40
	orr x7, x3, x3
	ldr x2, [sp, #1120]
	ldr x3, [sp, #1128]
	bl {vg_rsa_public_precomputed_checked}
	ldr x14, [sp, #32]
	bic x0, x0, x14, ror #0
	ldr x11, [sp, #16]
	ldr x12, [sp, #24]
	add x13, sp, #40
	movz x15, #0, lsl #0
24:
	ldrb w10, [x11, #0]
	bic x10, x10, x14, ror #0
	strb w10, [x11, #0]
	strb w15, [x13, #0]
	add x11, x11, #1
	add x13, x13, #1
	sub x12, x12, #1
	cbnz x12, 24b
	add sp, sp, #1072
	ldr x30, [sp], #16
	ret
	.p2align 6
