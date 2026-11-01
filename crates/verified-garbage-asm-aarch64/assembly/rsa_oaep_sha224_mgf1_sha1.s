// The functions of `src/rsa_oaep_sha224_mgf1_sha1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha224_mgf1_sha1_decrypt:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #216]
	str x3, [x9, #160]
	str x4, [x9, #168]
	str x5, [x9, #176]
	str x6, [x9, #184]
	str x7, [x9, #0]
	ldr x10, [sp, #360]
	str x10, [x9, #200]
	ldr x10, [sp, #368]
	str x10, [x9, #208]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x10, [sp, #400]
	str x10, [x9, #192]
	ldr x10, [sp, #288]
	str x10, [x9, #8]
	ldr x10, [sp, #296]
	str x10, [x9, #16]
	ldr x10, [sp, #304]
	str x10, [x9, #24]
	ldr x10, [sp, #312]
	str x10, [x9, #32]
	ldr x10, [sp, #320]
	str x10, [x9, #40]
	ldr x10, [sp, #328]
	str x10, [x9, #48]
	ldr x10, [sp, #336]
	str x10, [x9, #56]
	ldr x10, [sp, #344]
	str x10, [x9, #64]
	ldr x10, [sp, #352]
	str x10, [x9, #72]
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	str x10, [x9, #80]
	str x11, [x9, #88]
	ldr x0, [sp, #96]
	add x0, x0, #0
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #376]
	ldr x7, [sp, #168]
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
22:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
23:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 23b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 22b
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
24:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
25:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 25b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 24b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
27:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
28:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 28b
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
210:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
211:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 211b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
212:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 212b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
213:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 213b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #216]
	str x3, [x9, #160]
	str x4, [x9, #168]
	str x5, [x9, #176]
	str x6, [x9, #184]
	str x7, [x9, #0]
	ldr x10, [sp, #360]
	str x10, [x9, #200]
	ldr x10, [sp, #368]
	str x10, [x9, #208]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x10, [sp, #400]
	str x10, [x9, #192]
	ldr x10, [sp, #288]
	str x10, [x9, #8]
	ldr x10, [sp, #296]
	str x10, [x9, #16]
	ldr x10, [sp, #304]
	str x10, [x9, #24]
	ldr x10, [sp, #312]
	str x10, [x9, #32]
	ldr x10, [sp, #320]
	str x10, [x9, #40]
	ldr x10, [sp, #328]
	str x10, [x9, #48]
	ldr x10, [sp, #336]
	str x10, [x9, #56]
	ldr x10, [sp, #344]
	str x10, [x9, #64]
	ldr x10, [sp, #352]
	str x10, [x9, #72]
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	str x10, [x9, #80]
	str x11, [x9, #88]
	ldr x0, [sp, #96]
	add x0, x0, #0
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #376]
	ldr x7, [sp, #168]
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
22:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
23:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 23b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 22b
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
24:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
25:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 25b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 24b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
27:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
28:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 28b
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
210:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
211:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 211b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
212:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 212b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
213:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 213b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #216]
	str x3, [x9, #160]
	str x4, [x9, #168]
	str x5, [x9, #176]
	str x6, [x9, #184]
	str x7, [x9, #0]
	ldr x10, [sp, #360]
	str x10, [x9, #200]
	ldr x10, [sp, #368]
	str x10, [x9, #208]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x10, [sp, #400]
	str x10, [x9, #192]
	ldr x10, [sp, #288]
	str x10, [x9, #8]
	ldr x10, [sp, #296]
	str x10, [x9, #16]
	ldr x10, [sp, #304]
	str x10, [x9, #24]
	ldr x10, [sp, #312]
	str x10, [x9, #32]
	ldr x10, [sp, #320]
	str x10, [x9, #40]
	ldr x10, [sp, #328]
	str x10, [x9, #48]
	ldr x10, [sp, #336]
	str x10, [x9, #56]
	ldr x10, [sp, #344]
	str x10, [x9, #64]
	ldr x10, [sp, #352]
	str x10, [x9, #72]
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	str x10, [x9, #80]
	str x11, [x9, #88]
	ldr x0, [sp, #96]
	add x0, x0, #0
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #376]
	ldr x7, [sp, #168]
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
22:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
23:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 23b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 22b
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
24:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
25:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 25b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 24b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
27:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
28:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 28b
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
210:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
211:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 211b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
212:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 212b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
213:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 213b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2_mgf1_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #216]
	str x3, [x9, #160]
	str x4, [x9, #168]
	str x5, [x9, #176]
	str x6, [x9, #184]
	str x7, [x9, #0]
	ldr x10, [sp, #360]
	str x10, [x9, #200]
	ldr x10, [sp, #368]
	str x10, [x9, #208]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x10, [sp, #400]
	str x10, [x9, #192]
	ldr x10, [sp, #288]
	str x10, [x9, #8]
	ldr x10, [sp, #296]
	str x10, [x9, #16]
	ldr x10, [sp, #304]
	str x10, [x9, #24]
	ldr x10, [sp, #312]
	str x10, [x9, #32]
	ldr x10, [sp, #320]
	str x10, [x9, #40]
	ldr x10, [sp, #328]
	str x10, [x9, #48]
	ldr x10, [sp, #336]
	str x10, [x9, #56]
	ldr x10, [sp, #344]
	str x10, [x9, #64]
	ldr x10, [sp, #352]
	str x10, [x9, #72]
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	str x10, [x9, #80]
	str x11, [x9, #88]
	ldr x0, [sp, #96]
	add x0, x0, #0
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #376]
	ldr x7, [sp, #168]
	bl {vg_rsa_private_checked}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3392
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
22:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
23:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 23b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 22b
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
24:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
25:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 25b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 24b
	ldr x11, [sp, #96]
	add x11, x11, #3392
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #96]
	add x13, x13, #0
	ldrb w14, [x13, #0]
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x10, x10, x15
	orr x14, x14, x10
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	add x9, sp, #0
	str x14, [x9, #232]
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	movz x13, #0, lsl #0
	sub x13, x13, #1
	movz x8, #0, lsl #0
	ldr x14, [sp, #232]
	movz x9, #0, lsl #0
	movz x17, #1, lsl #0
27:
	ldrb w10, [x11, #0]
	subs x15, x10, x17
	sbc x15, x15, x15
	eor x16, x10, x17
	subs x16, x16, x17
	sbc x16, x16, x16
	orr x10, x15, x16
	bic x10, x13, x10, ror #0
	orr x14, x14, x10
	and x10, x9, x13
	and x10, x10, x16
	orr x8, x8, x10
	bic x13, x13, x16, ror #0
	add x9, x9, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	orr x14, x14, x13
	add x9, sp, #0
	str x14, [x9, #232]
	str x8, [x9, #240]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	movz x12, #256, lsl #0
	movz x13, #0, lsl #0
28:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 28b
	ldr x11, [sp, #96]
	add x11, x11, #57
	ldr x12, [sp, #168]
	sub x12, x12, #57
	orr x13, x12, x12
	orr x10, x11, x11
	ldr x12, [sp, #96]
	add x12, x12, #1024
	orr x11, x10, x10
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #240]
	add x9, x9, #1
	movz x14, #1, lsl #0
	movz x8, #10, lsl #0
210:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	movz x13, #128, lsl #0
211:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 211b
	lsr x9, x9, #1
	add x14, x14, x14
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x10, [sp, #224]
	movz x17, #1, lsl #0
	eor x10, x10, x17
	subs x10, x10, x17
	sbc x10, x10, x10
	ldr x11, [sp, #232]
	subs x11, x11, x17
	sbc x11, x11, x11
	and x11, x11, x10
	add x9, sp, #0
	str x11, [x9, #248]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x11, [sp, #152]
	ldr x13, [sp, #168]
	ldr x15, [sp, #248]
212:
	ldrb w10, [x12, #0]
	and x10, x10, x15
	strb w10, [x11, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 212b
	ldr x14, [sp, #248]
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x11, [sp, #240]
	sub x10, x10, x11
	and x10, x10, x14
	ldr x11, [sp, #216]
	str x10, [x11, #0]
	movz x15, #1, lsl #0
	and x14, x14, x15
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
	orr x0, x0, x14
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
213:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 213b
	ldr x11, [sp, #216]
	str x13, [x11, #0]
	ldr x10, [sp, #224]
	movz x12, #2, lsl #0
	eor x10, x10, x12
	movz x13, #1, lsl #0
	subs x10, x10, x13
	sbc x10, x10, x10
	and x0, x10, x12
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #160]
	str x3, [x9, #168]
	str x4, [x9, #176]
	str x5, [x9, #184]
	str x6, [x9, #200]
	str x7, [x9, #208]
	ldr x10, [sp, #288]
	str x10, [x9, #216]
	ldr x10, [sp, #296]
	str x10, [x9, #224]
	ldr x10, [sp, #304]
	str x10, [x9, #232]
	ldr x10, [sp, #312]
	str x10, [x9, #96]
	ldr x10, [sp, #320]
	str x10, [x9, #192]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 22f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
24:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 24b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
25:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 25b
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #29
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 27f
	b 28f
27:
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
28:
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
210:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
211:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 211b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 210b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
212:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
213:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 213b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 212b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #328]
	ldr x3, [sp, #336]
	bl {vg_rsa_public_precomputed_checked}
	b 23f
22:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
214:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 214b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
215:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 215b
	movz x0, #0, lsl #0
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_mgf1_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #160]
	str x3, [x9, #168]
	str x4, [x9, #176]
	str x5, [x9, #184]
	str x6, [x9, #200]
	str x7, [x9, #208]
	ldr x10, [sp, #288]
	str x10, [x9, #216]
	ldr x10, [sp, #296]
	str x10, [x9, #224]
	ldr x10, [sp, #304]
	str x10, [x9, #232]
	ldr x10, [sp, #312]
	str x10, [x9, #96]
	ldr x10, [sp, #320]
	str x10, [x9, #192]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 22f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
24:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 24b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
25:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 25b
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #29
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 27f
	b 28f
27:
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
28:
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
210:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
211:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 211b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 210b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
212:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
213:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 213b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 212b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #328]
	ldr x3, [sp, #336]
	bl {vg_rsa_public_precomputed_checked}
	b 23f
22:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
214:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 214b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
215:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 215b
	movz x0, #0, lsl #0
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #160]
	str x3, [x9, #168]
	str x4, [x9, #176]
	str x5, [x9, #184]
	str x6, [x9, #200]
	str x7, [x9, #208]
	ldr x10, [sp, #288]
	str x10, [x9, #216]
	ldr x10, [sp, #296]
	str x10, [x9, #224]
	ldr x10, [sp, #304]
	str x10, [x9, #232]
	ldr x10, [sp, #312]
	str x10, [x9, #96]
	ldr x10, [sp, #320]
	str x10, [x9, #192]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 22f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
24:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 24b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
25:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 25b
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #29
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 27f
	b 28f
27:
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
28:
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
210:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
211:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 211b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 210b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
212:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
213:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 213b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 212b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #328]
	ldr x3, [sp, #336]
	bl {vg_rsa_public_precomputed_checked}
	b 23f
22:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
214:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 214b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
215:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 215b
	movz x0, #0, lsl #0
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_sha2_mgf1_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x2, [x9, #160]
	str x3, [x9, #168]
	str x4, [x9, #176]
	str x5, [x9, #184]
	str x6, [x9, #200]
	str x7, [x9, #208]
	ldr x10, [sp, #288]
	str x10, [x9, #216]
	ldr x10, [sp, #296]
	str x10, [x9, #224]
	ldr x10, [sp, #304]
	str x10, [x9, #232]
	ldr x10, [sp, #312]
	str x10, [x9, #96]
	ldr x10, [sp, #320]
	str x10, [x9, #192]
	ldr x10, [sp, #168]
	movz x12, #58, lsl #0
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 20f
	ldr x10, [sp, #168]
	sub x10, x10, #58
	ldr x12, [sp, #224]
	subs x11, x10, x12
	sbc x11, x11, x11
	cbnz x11, 22f
	ldr x11, [sp, #96]
	add x11, x11, #0
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
24:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 24b
	ldr x11, [sp, #232]
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
25:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 25b
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha224_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #200]
	ldr x3, [sp, #208]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #208]
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x12, [sp, #96]
	add x12, x12, #29
	movz x13, #28, lsl #0
26:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	ldr x11, [sp, #216]
	ldr x12, [sp, #96]
	add x12, x12, #0
	ldr x10, [sp, #168]
	add x12, x12, x10
	ldr x13, [sp, #224]
	sub x12, x12, x13
	sub x12, x12, #1
	movz x10, #1, lsl #0
	strb w10, [x12, #0]
	add x12, x12, #1
	cbnz x13, 27f
	b 28f
27:
29:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 29b
28:
	ldr x10, [sp, #96]
	add x10, x10, #29
	ldr x11, [sp, #168]
	sub x11, x11, #29
	ldr x12, [sp, #96]
	add x12, x12, #1
	movz x13, #28, lsl #0
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
210:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
211:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 211b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 210b
	ldr x10, [sp, #96]
	add x10, x10, #1
	movz x11, #28, lsl #0
	ldr x12, [sp, #96]
	add x12, x12, #29
	ldr x13, [sp, #168]
	sub x13, x13, #29
	add x9, sp, #0
	str x10, [x9, #120]
	str x11, [x9, #128]
	str x12, [x9, #104]
	str x13, [x9, #112]
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #136]
	str x10, [x9, #144]
212:
	ldr x0, [sp, #96]
	add x0, x0, #3072
	bl {vg_sha1_init}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	movz x1, #0, lsl #0
	ldr x2, [sp, #104]
	ldr x3, [sp, #112]
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x2, [sp, #96]
	add x2, x2, #3456
	ldr x10, [sp, #136]
	strb w10, [x2, #3]
	lsr x10, x10, #8
	strb w10, [x2, #2]
	lsr x10, x10, #8
	strb w10, [x2, #1]
	lsr x10, x10, #8
	strb w10, [x2, #0]
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	movz x3, #4, lsl #0
	ldr x4, [sp, #96]
	add x4, x4, #3520
	bl {vg_sha1_update_scratch_sha2}
	ldr x0, [sp, #96]
	add x0, x0, #3072
	ldr x1, [sp, #112]
	add x1, x1, #4
	ldr x2, [sp, #96]
	add x2, x2, #3328
	ldr x3, [sp, #96]
	add x3, x3, #3520
	bl {vg_sha1_finalize_scratch_sha2}
	ldr x11, [sp, #96]
	add x11, x11, #3328
	ldr x10, [sp, #144]
	ldr x12, [sp, #120]
	add x12, x12, x10
	ldr x13, [sp, #128]
	sub x13, x13, x10
	movz x14, #20, lsl #0
	subs x15, x13, x14
	csel x14, x14, x13, hs
213:
	ldrb w10, [x11, #0]
	ldrb w15, [x12, #0]
	eor x15, x15, x10
	strb w15, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x14, x14, #1
	cbnz x14, 213b
	add x9, sp, #0
	ldr x10, [sp, #136]
	add x10, x10, #1
	str x10, [x9, #136]
	ldr x10, [sp, #144]
	add x10, x10, #20
	str x10, [x9, #144]
	ldr x11, [sp, #128]
	subs x12, x10, x11
	sbc x12, x12, x12
	cbnz x12, 212b
	ldr x10, [sp, #96]
	movz x15, #8192, lsl #0
	add x10, x10, x15
	ldr x11, [sp, #192]
	sub x11, x11, #1024
	add x9, sp, #0
	str x10, [x9, #0]
	str x11, [x9, #8]
	ldr x0, [sp, #152]
	ldr x1, [sp, #168]
	ldr x2, [sp, #160]
	ldr x3, [sp, #168]
	ldr x4, [sp, #176]
	ldr x5, [sp, #184]
	ldr x6, [sp, #96]
	add x6, x6, #0
	ldr x7, [sp, #168]
	ldr x2, [sp, #328]
	ldr x3, [sp, #336]
	bl {vg_rsa_public_precomputed_checked}
	b 23f
22:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
214:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 214b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x11, [sp, #152]
	ldr x12, [sp, #168]
	movz x13, #0, lsl #0
215:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 215b
	movz x0, #0, lsl #0
21:
	add sp, sp, #272
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6
