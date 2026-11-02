// The functions of `src/rsa_pss_md5_mgf1_md5.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_md5_mgf1_md5_sign:
	sub sp, sp, #336
	add x16, sp, #0
	str x19, [x16, #96]
	str x20, [x16, #104]
	str x21, [x16, #112]
	str x22, [x16, #120]
	str x23, [x16, #128]
	str x24, [x16, #136]
	str x25, [x16, #144]
	str x26, [x16, #152]
	str x27, [x16, #160]
	str x28, [x16, #168]
	str x30, [x16, #176]
	str x0, [x16, #216]
	str x2, [x16, #184]
	str x4, [x16, #192]
	str x5, [x16, #200]
	str x6, [x16, #288]
	str x7, [x16, #296]
	add x23, x3, #0
	ldr x9, [sp, #400]
	str x9, [x16, #208]
	ldr x9, [sp, #408]
	str x9, [x16, #224]
	ldr x9, [sp, #416]
	str x9, [x16, #232]
	ldr x20, [sp, #424]
	ldr x9, [sp, #432]
	str x9, [x16, #240]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x2, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x0, x20, #2560
	movz x9, #0, lsl #0
	strb w9, [x0, #0]
	add x0, x0, x26
	add x1, x25, #0
	ldr x2, [sp, #208]
	ldr x3, [sp, #224]
	ldr x4, [sp, #232]
	add x5, x24, #0
	add x6, x20, #3584
	ldr x7, [sp, #240]
	sub x7, x7, #448
	bl {vg_rsa_pss_md5_mgf1_md5_encode}
	cbz w0, 22f
	add x16, sp, #0
	ldr x9, [sp, #288]
	str x9, [x16, #0]
	ldr x9, [sp, #296]
	str x9, [x16, #8]
	ldr x9, [sp, #336]
	str x9, [x16, #16]
	ldr x9, [sp, #344]
	str x9, [x16, #24]
	ldr x9, [sp, #352]
	str x9, [x16, #32]
	ldr x9, [sp, #360]
	str x9, [x16, #40]
	ldr x9, [sp, #368]
	str x9, [x16, #48]
	ldr x9, [sp, #376]
	str x9, [x16, #56]
	ldr x9, [sp, #384]
	str x9, [x16, #64]
	ldr x9, [sp, #392]
	str x9, [x16, #72]
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #80]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #88]
	ldr x0, [sp, #216]
	add x1, x23, #0
	ldr x2, [sp, #184]
	add x3, x23, #0
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	add x6, x20, #2560
	add x7, x23, #0
	bl {vg_rsa_private_checked}
	b 23f
22:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
24:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 24b
	movz x0, #0, lsl #0
23:
	b 21f
20:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
25:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 25b
	movz x0, #0, lsl #0
21:
	add x16, sp, #0
	ldr x19, [x16, #96]
	ldr x20, [x16, #104]
	ldr x21, [x16, #112]
	ldr x22, [x16, #120]
	ldr x23, [x16, #128]
	ldr x24, [x16, #136]
	ldr x25, [x16, #144]
	ldr x26, [x16, #152]
	ldr x27, [x16, #160]
	ldr x28, [x16, #168]
	ldr x30, [x16, #176]
	add sp, sp, #336
	ret
	.p2align 6

vg_rsa_pss_md5_mgf1_md5_verify_precomputed:
	sub sp, sp, #336
	add x16, sp, #0
	str x19, [x16, #96]
	str x20, [x16, #104]
	str x21, [x16, #112]
	str x22, [x16, #120]
	str x23, [x16, #128]
	str x24, [x16, #136]
	str x25, [x16, #144]
	str x26, [x16, #152]
	str x27, [x16, #160]
	str x28, [x16, #168]
	str x30, [x16, #176]
	str x0, [x16, #184]
	str x2, [x16, #192]
	str x3, [x16, #200]
	str x4, [x16, #208]
	str x5, [x16, #216]
	str x7, [x16, #232]
	add x23, x1, #0
	ldr x9, [sp, #336]
	add w9, w9, #0
	str x9, [x16, #264]
	ldr x20, [sp, #344]
	ldr x9, [sp, #352]
	str x9, [x16, #240]
	ldr x9, [sp, #360]
	str x9, [x16, #312]
	ldr x9, [sp, #368]
	str x9, [x16, #320]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x0, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x16, sp, #0
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #0]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #8]
	add x0, x20, #0
	add x1, x23, #0
	ldr x2, [sp, #312]
	ldr x3, [sp, #320]
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	ldr x6, [sp, #216]
	add x7, x23, #0
	bl {vg_rsa_public_precomputed_checked}
	add x1, x20, x26
	ldrb w9, [x20, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x26
	and x9, x9, x10
	sub x26, x9, #1
	lsr x26, x26, #63
	ldr x0, [sp, #208]
	add x2, x25, #0
	add x3, x24, #0
	ldr x4, [sp, #232]
	ldr x5, [sp, #264]
	add x9, x23, #7
	lsr x9, x9, #3
	ldr x7, [sp, #240]
	sub x7, x7, x9
	lsl x9, x9, #3
	add x6, x20, x9
	bl {vg_rsa_pss_md5_mgf1_md5_check_encoding}
	and x0, x0, x26
	b 21f
20:
	movz x0, #0, lsl #0
21:
	add x16, sp, #0
	ldr x19, [x16, #96]
	ldr x20, [x16, #104]
	ldr x21, [x16, #112]
	ldr x22, [x16, #120]
	ldr x23, [x16, #128]
	ldr x24, [x16, #136]
	ldr x25, [x16, #144]
	ldr x26, [x16, #152]
	ldr x27, [x16, #160]
	ldr x28, [x16, #168]
	ldr x30, [x16, #176]
	add sp, sp, #336
	ret
	.p2align 6
