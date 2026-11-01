// The functions of `src/hmac_sha1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init:
	movz x10, #64, lsl #0
	movz x12, #0, lsl #0
	subs x11, x10, x3
	csel x9, x12, x3, hs
	cbnz x9, 20f
	sub sp, sp, #448
	add x4, sp, #0
	str x19, [x4, #160]
	str x20, [x4, #168]
	str x21, [x4, #176]
	str x22, [x4, #184]
	str x24, [x4, #192]
	str x30, [x4, #200]
	str x23, [x4, #208]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha1_init}
	add x0, x21, #0
	bl {vg_sha1_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #20]
	str w14, [x19, #24]
	str w14, [x19, #28]
	str w14, [x19, #32]
	str w14, [x19, #36]
	str w14, [x19, #40]
	str w14, [x19, #44]
	str w14, [x19, #48]
	str w14, [x19, #52]
	str w14, [x19, #56]
	str w14, [x19, #60]
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	movz x10, #0, lsl #0
	cbz x24, 22f
24:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #20]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 24b
	b 23f
22:
23:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
	ldr w9, [x19, #20]
	eor x9, x9, x15
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	eor x9, x9, x15
	str w9, [x21, #24]
	ldr w9, [x19, #28]
	eor x9, x9, x15
	str w9, [x21, #28]
	ldr w9, [x19, #32]
	eor x9, x9, x15
	str w9, [x21, #32]
	ldr w9, [x19, #36]
	eor x9, x9, x15
	str w9, [x21, #36]
	ldr w9, [x19, #40]
	eor x9, x9, x15
	str w9, [x21, #40]
	ldr w9, [x19, #44]
	eor x9, x9, x15
	str w9, [x21, #44]
	ldr w9, [x19, #48]
	eor x9, x9, x15
	str w9, [x21, #48]
	ldr w9, [x19, #52]
	eor x9, x9, x15
	str w9, [x21, #52]
	ldr w9, [x19, #56]
	eor x9, x9, x15
	str w9, [x21, #56]
	ldr w9, [x19, #60]
	eor x9, x9, x15
	str w9, [x21, #60]
	ldr w9, [x19, #64]
	eor x9, x9, x15
	str w9, [x21, #64]
	ldr w9, [x19, #68]
	eor x9, x9, x15
	str w9, [x21, #68]
	ldr w9, [x19, #72]
	eor x9, x9, x15
	str w9, [x21, #72]
	ldr w9, [x19, #76]
	eor x9, x9, x15
	str w9, [x21, #76]
	ldr w9, [x19, #80]
	eor x9, x9, x15
	str w9, [x21, #80]
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	add x19, x21, #0
	add x1, x21, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	ldr x19, [x23, #160]
	ldr x20, [x23, #168]
	ldr x21, [x23, #176]
	ldr x22, [x23, #184]
	ldr x24, [x23, #192]
	ldr x30, [x23, #200]
	ldr x23, [x23, #208]
	add sp, sp, #448
21:
	ret
20:
	sub sp, sp, #1120
	add x4, sp, #0
	str x19, [x4, #448]
	str x20, [x4, #456]
	str x21, [x4, #464]
	str x22, [x4, #472]
	str x24, [x4, #480]
	str x30, [x4, #488]
	str x23, [x4, #496]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #6
	cbz x9, 25f
	sub x9, x20, #64
	cbz x9, 27f
	add x0, x23, #780
	bl {vg_sha1_init}
	add x0, x23, #780
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch}
	add x0, x23, #780
	add x1, x20, #0
	add x2, x23, #904
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch}
	add x2, x23, #904
	movz x3, #20, lsl #0
	b 28f
27:
	add x2, x19, #0
	add x3, x20, #0
28:
	b 26f
25:
	add x2, x19, #0
	add x3, x20, #0
26:
	add x0, x21, #0
	add x1, x22, #0
	add x4, x23, #0
	bl {vg_hmac_sha1_init_scratch}
	ldr x19, [x23, #448]
	ldr x20, [x23, #456]
	ldr x21, [x23, #464]
	ldr x22, [x23, #472]
	ldr x24, [x23, #480]
	ldr x30, [x23, #488]
	ldr x23, [x23, #496]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add sp, sp, #1120
	b 21b
	.p2align 6

vg_hmac_sha1_finalize:
	sub sp, sp, #448
	add x4, sp, #0
	str x19, [x4, #160]
	str x20, [x4, #168]
	str x21, [x4, #176]
	str x22, [x4, #184]
	str x24, [x4, #192]
	str x30, [x4, #200]
	str x23, [x4, #208]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #216
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch}
	ldr w9, [x20, #0]
	str w9, [x19, #0]
	ldr w9, [x20, #4]
	str w9, [x19, #4]
	ldr w9, [x20, #8]
	str w9, [x19, #8]
	ldr w9, [x20, #12]
	str w9, [x19, #12]
	ldr w9, [x20, #16]
	str w9, [x19, #16]
	ldr w9, [x23, #216]
	str w9, [x19, #20]
	ldr w9, [x23, #220]
	str w9, [x19, #24]
	ldr w9, [x23, #224]
	str w9, [x19, #28]
	ldr w9, [x23, #228]
	str w9, [x19, #32]
	ldr w9, [x23, #232]
	str w9, [x19, #36]
	add x24, x21, #0
	add x21, x19, #20
	add x20, x23, #0
	movz x9, #128, lsl #0
	str w9, [x21, #20]
	movz x9, #0, lsl #0
	str w9, [x21, #24]
	str w9, [x21, #28]
	str w9, [x21, #32]
	str w9, [x21, #36]
	str w9, [x21, #40]
	str w9, [x21, #44]
	str w9, [x21, #48]
	str w9, [x21, #52]
	movz x22, #84, lsl #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	add x21, x24, #0
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x23, #160]
	ldr x20, [x23, #168]
	ldr x21, [x23, #176]
	ldr x22, [x23, #184]
	ldr x24, [x23, #192]
	ldr x30, [x23, #200]
	ldr x23, [x23, #208]
	add sp, sp, #448
	ret
	.p2align 6

vg_hmac_sha1_init_sha2:
	.arch_extension sha2
	movz x10, #64, lsl #0
	movz x12, #0, lsl #0
	subs x11, x10, x3
	csel x9, x12, x3, hs
	cbnz x9, 20f
	sub sp, sp, #448
	add x4, sp, #0
	str x19, [x4, #160]
	str x20, [x4, #168]
	str x21, [x4, #176]
	str x22, [x4, #184]
	str x24, [x4, #192]
	str x30, [x4, #200]
	str x23, [x4, #208]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha1_init}
	add x0, x21, #0
	bl {vg_sha1_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #20]
	str w14, [x19, #24]
	str w14, [x19, #28]
	str w14, [x19, #32]
	str w14, [x19, #36]
	str w14, [x19, #40]
	str w14, [x19, #44]
	str w14, [x19, #48]
	str w14, [x19, #52]
	str w14, [x19, #56]
	str w14, [x19, #60]
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	movz x10, #0, lsl #0
	cbz x24, 22f
24:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #20]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 24b
	b 23f
22:
23:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
	ldr w9, [x19, #20]
	eor x9, x9, x15
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	eor x9, x9, x15
	str w9, [x21, #24]
	ldr w9, [x19, #28]
	eor x9, x9, x15
	str w9, [x21, #28]
	ldr w9, [x19, #32]
	eor x9, x9, x15
	str w9, [x21, #32]
	ldr w9, [x19, #36]
	eor x9, x9, x15
	str w9, [x21, #36]
	ldr w9, [x19, #40]
	eor x9, x9, x15
	str w9, [x21, #40]
	ldr w9, [x19, #44]
	eor x9, x9, x15
	str w9, [x21, #44]
	ldr w9, [x19, #48]
	eor x9, x9, x15
	str w9, [x21, #48]
	ldr w9, [x19, #52]
	eor x9, x9, x15
	str w9, [x21, #52]
	ldr w9, [x19, #56]
	eor x9, x9, x15
	str w9, [x21, #56]
	ldr w9, [x19, #60]
	eor x9, x9, x15
	str w9, [x21, #60]
	ldr w9, [x19, #64]
	eor x9, x9, x15
	str w9, [x21, #64]
	ldr w9, [x19, #68]
	eor x9, x9, x15
	str w9, [x21, #68]
	ldr w9, [x19, #72]
	eor x9, x9, x15
	str w9, [x21, #72]
	ldr w9, [x19, #76]
	eor x9, x9, x15
	str w9, [x21, #76]
	ldr w9, [x19, #80]
	eor x9, x9, x15
	str w9, [x21, #80]
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x19, x21, #0
	add x1, x21, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	ldr x19, [x23, #160]
	ldr x20, [x23, #168]
	ldr x21, [x23, #176]
	ldr x22, [x23, #184]
	ldr x24, [x23, #192]
	ldr x30, [x23, #200]
	ldr x23, [x23, #208]
	add sp, sp, #448
21:
	ret
20:
	sub sp, sp, #1120
	add x4, sp, #0
	str x19, [x4, #448]
	str x20, [x4, #456]
	str x21, [x4, #464]
	str x22, [x4, #472]
	str x24, [x4, #480]
	str x30, [x4, #488]
	str x23, [x4, #496]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #6
	cbz x9, 25f
	sub x9, x20, #64
	cbz x9, 27f
	add x0, x23, #780
	bl {vg_sha1_init}
	add x0, x23, #780
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch_sha2}
	add x0, x23, #780
	add x1, x20, #0
	add x2, x23, #904
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch_sha2}
	add x2, x23, #904
	movz x3, #20, lsl #0
	b 28f
27:
	add x2, x19, #0
	add x3, x20, #0
28:
	b 26f
25:
	add x2, x19, #0
	add x3, x20, #0
26:
	add x0, x21, #0
	add x1, x22, #0
	add x4, x23, #0
	bl {vg_hmac_sha1_init_scratch_sha2}
	ldr x19, [x23, #448]
	ldr x20, [x23, #456]
	ldr x21, [x23, #464]
	ldr x22, [x23, #472]
	ldr x24, [x23, #480]
	ldr x30, [x23, #488]
	ldr x23, [x23, #496]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add sp, sp, #1120
	b 21b
	.arch_extension nosha2
	.p2align 6

vg_hmac_sha1_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #448
	add x4, sp, #0
	str x19, [x4, #160]
	str x20, [x4, #168]
	str x21, [x4, #176]
	str x22, [x4, #184]
	str x24, [x4, #192]
	str x30, [x4, #200]
	str x23, [x4, #208]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #216
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch_sha2}
	ldr w9, [x20, #0]
	str w9, [x19, #0]
	ldr w9, [x20, #4]
	str w9, [x19, #4]
	ldr w9, [x20, #8]
	str w9, [x19, #8]
	ldr w9, [x20, #12]
	str w9, [x19, #12]
	ldr w9, [x20, #16]
	str w9, [x19, #16]
	ldr w9, [x23, #216]
	str w9, [x19, #20]
	ldr w9, [x23, #220]
	str w9, [x19, #24]
	ldr w9, [x23, #224]
	str w9, [x19, #28]
	ldr w9, [x23, #228]
	str w9, [x19, #32]
	ldr w9, [x23, #232]
	str w9, [x19, #36]
	add x24, x21, #0
	add x21, x19, #20
	add x20, x23, #0
	movz x9, #128, lsl #0
	str w9, [x21, #20]
	movz x9, #0, lsl #0
	str w9, [x21, #24]
	str w9, [x21, #28]
	str w9, [x21, #32]
	str w9, [x21, #36]
	str w9, [x21, #40]
	str w9, [x21, #44]
	str w9, [x21, #48]
	str w9, [x21, #52]
	movz x22, #84, lsl #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x21, x24, #0
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x23, #160]
	ldr x20, [x23, #168]
	ldr x21, [x23, #176]
	ldr x22, [x23, #184]
	ldr x24, [x23, #192]
	ldr x30, [x23, #200]
	ldr x23, [x23, #208]
	add sp, sp, #448
	ret
	.arch_extension nosha2
	.p2align 6
