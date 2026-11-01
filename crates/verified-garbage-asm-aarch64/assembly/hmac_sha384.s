// The functions of `src/hmac_sha384.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_init:
	movz x10, #128, lsl #0
	movz x12, #0, lsl #0
	subs x11, x10, x3
	csel x9, x12, x3, hs
	cbnz x9, 20f
	sub sp, sp, #1872
	add x4, sp, #0
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha384_init}
	add x0, x21, #0
	bl {vg_sha384_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	str w14, [x19, #84]
	str w14, [x19, #88]
	str w14, [x19, #92]
	str w14, [x19, #96]
	str w14, [x19, #100]
	str w14, [x19, #104]
	str w14, [x19, #108]
	str w14, [x19, #112]
	str w14, [x19, #116]
	str w14, [x19, #120]
	str w14, [x19, #124]
	str w14, [x19, #128]
	str w14, [x19, #132]
	str w14, [x19, #136]
	str w14, [x19, #140]
	str w14, [x19, #144]
	str w14, [x19, #148]
	str w14, [x19, #152]
	str w14, [x19, #156]
	str w14, [x19, #160]
	str w14, [x19, #164]
	str w14, [x19, #168]
	str w14, [x19, #172]
	str w14, [x19, #176]
	str w14, [x19, #180]
	str w14, [x19, #184]
	str w14, [x19, #188]
	movz x10, #0, lsl #0
	cbz x24, 22f
24:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #64]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 24b
	b 23f
22:
23:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
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
	ldr w9, [x19, #84]
	eor x9, x9, x15
	str w9, [x21, #84]
	ldr w9, [x19, #88]
	eor x9, x9, x15
	str w9, [x21, #88]
	ldr w9, [x19, #92]
	eor x9, x9, x15
	str w9, [x21, #92]
	ldr w9, [x19, #96]
	eor x9, x9, x15
	str w9, [x21, #96]
	ldr w9, [x19, #100]
	eor x9, x9, x15
	str w9, [x21, #100]
	ldr w9, [x19, #104]
	eor x9, x9, x15
	str w9, [x21, #104]
	ldr w9, [x19, #108]
	eor x9, x9, x15
	str w9, [x21, #108]
	ldr w9, [x19, #112]
	eor x9, x9, x15
	str w9, [x21, #112]
	ldr w9, [x19, #116]
	eor x9, x9, x15
	str w9, [x21, #116]
	ldr w9, [x19, #120]
	eor x9, x9, x15
	str w9, [x21, #120]
	ldr w9, [x19, #124]
	eor x9, x9, x15
	str w9, [x21, #124]
	ldr w9, [x19, #128]
	eor x9, x9, x15
	str w9, [x21, #128]
	ldr w9, [x19, #132]
	eor x9, x9, x15
	str w9, [x21, #132]
	ldr w9, [x19, #136]
	eor x9, x9, x15
	str w9, [x21, #136]
	ldr w9, [x19, #140]
	eor x9, x9, x15
	str w9, [x21, #140]
	ldr w9, [x19, #144]
	eor x9, x9, x15
	str w9, [x21, #144]
	ldr w9, [x19, #148]
	eor x9, x9, x15
	str w9, [x21, #148]
	ldr w9, [x19, #152]
	eor x9, x9, x15
	str w9, [x21, #152]
	ldr w9, [x19, #156]
	eor x9, x9, x15
	str w9, [x21, #156]
	ldr w9, [x19, #160]
	eor x9, x9, x15
	str w9, [x21, #160]
	ldr w9, [x19, #164]
	eor x9, x9, x15
	str w9, [x21, #164]
	ldr w9, [x19, #168]
	eor x9, x9, x15
	str w9, [x21, #168]
	ldr w9, [x19, #172]
	eor x9, x9, x15
	str w9, [x21, #172]
	ldr w9, [x19, #176]
	eor x9, x9, x15
	str w9, [x21, #176]
	ldr w9, [x19, #180]
	eor x9, x9, x15
	str w9, [x21, #180]
	ldr w9, [x19, #184]
	eor x9, x9, x15
	str w9, [x21, #184]
	ldr w9, [x19, #188]
	eor x9, x9, x15
	str w9, [x21, #188]
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	add x19, x21, #0
	add x1, x21, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	add sp, sp, #1872
21:
	ret
20:
	sub sp, sp, #3408
	add x4, sp, #0
	str x19, [x4, #1872]
	str x20, [x4, #1880]
	str x21, [x4, #1888]
	str x22, [x4, #1896]
	str x24, [x4, #1904]
	str x30, [x4, #1912]
	str x23, [x4, #1920]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #7
	cbz x9, 25f
	sub x9, x20, #128
	cbz x9, 27f
	add x0, x23, #2528
	bl {vg_sha384_init}
	add x0, x23, #2528
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch}
	add x0, x23, #2528
	add x1, x20, #0
	add x2, x23, #2816
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch}
	add x2, x23, #2816
	movz x3, #48, lsl #0
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
	bl {vg_hmac_sha384_init_scratch}
	ldr x19, [x23, #1872]
	ldr x20, [x23, #1880]
	ldr x21, [x23, #1888]
	ldr x22, [x23, #1896]
	ldr x24, [x23, #1904]
	ldr x30, [x23, #1912]
	ldr x23, [x23, #1920]
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3408
	b 21b
	.p2align 6

vg_hmac_sha384_finalize:
	sub sp, sp, #1872
	add x4, sp, #0
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #744
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch}
	ldp x9, x10, [x20, #0]
	stp x9, x10, [x19, #0]
	ldp x9, x10, [x20, #16]
	stp x9, x10, [x19, #16]
	ldp x9, x10, [x20, #32]
	stp x9, x10, [x19, #32]
	ldp x9, x10, [x20, #48]
	stp x9, x10, [x19, #48]
	ldr x9, [x23, #744]
	ldr x10, [x23, #752]
	stp x9, x10, [x19, #64]
	ldr x9, [x23, #760]
	ldr x10, [x23, #768]
	stp x9, x10, [x19, #80]
	ldr x9, [x23, #776]
	ldr x10, [x23, #784]
	stp x9, x10, [x19, #96]
	add x24, x21, #0
	add x21, x19, #64
	add x20, x23, #0
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x21, #48]
	stp x10, x10, [x21, #64]
	stp x10, x10, [x21, #80]
	stp x10, x10, [x21, #96]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldp x9, x10, [x21, #0]
	stp x9, x10, [x24, #0]
	ldp x9, x10, [x21, #16]
	stp x9, x10, [x24, #16]
	ldp x9, x10, [x21, #32]
	stp x9, x10, [x24, #32]
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	add sp, sp, #1872
	ret
	.p2align 6

vg_hmac_sha384_init_scratch:
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha384_init}
	add x0, x21, #0
	bl {vg_sha384_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	str w14, [x19, #84]
	str w14, [x19, #88]
	str w14, [x19, #92]
	str w14, [x19, #96]
	str w14, [x19, #100]
	str w14, [x19, #104]
	str w14, [x19, #108]
	str w14, [x19, #112]
	str w14, [x19, #116]
	str w14, [x19, #120]
	str w14, [x19, #124]
	str w14, [x19, #128]
	str w14, [x19, #132]
	str w14, [x19, #136]
	str w14, [x19, #140]
	str w14, [x19, #144]
	str w14, [x19, #148]
	str w14, [x19, #152]
	str w14, [x19, #156]
	str w14, [x19, #160]
	str w14, [x19, #164]
	str w14, [x19, #168]
	str w14, [x19, #172]
	str w14, [x19, #176]
	str w14, [x19, #180]
	str w14, [x19, #184]
	str w14, [x19, #188]
	movz x10, #0, lsl #0
	cbz x24, 20f
22:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #64]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 22b
	b 21f
20:
21:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
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
	ldr w9, [x19, #84]
	eor x9, x9, x15
	str w9, [x21, #84]
	ldr w9, [x19, #88]
	eor x9, x9, x15
	str w9, [x21, #88]
	ldr w9, [x19, #92]
	eor x9, x9, x15
	str w9, [x21, #92]
	ldr w9, [x19, #96]
	eor x9, x9, x15
	str w9, [x21, #96]
	ldr w9, [x19, #100]
	eor x9, x9, x15
	str w9, [x21, #100]
	ldr w9, [x19, #104]
	eor x9, x9, x15
	str w9, [x21, #104]
	ldr w9, [x19, #108]
	eor x9, x9, x15
	str w9, [x21, #108]
	ldr w9, [x19, #112]
	eor x9, x9, x15
	str w9, [x21, #112]
	ldr w9, [x19, #116]
	eor x9, x9, x15
	str w9, [x21, #116]
	ldr w9, [x19, #120]
	eor x9, x9, x15
	str w9, [x21, #120]
	ldr w9, [x19, #124]
	eor x9, x9, x15
	str w9, [x21, #124]
	ldr w9, [x19, #128]
	eor x9, x9, x15
	str w9, [x21, #128]
	ldr w9, [x19, #132]
	eor x9, x9, x15
	str w9, [x21, #132]
	ldr w9, [x19, #136]
	eor x9, x9, x15
	str w9, [x21, #136]
	ldr w9, [x19, #140]
	eor x9, x9, x15
	str w9, [x21, #140]
	ldr w9, [x19, #144]
	eor x9, x9, x15
	str w9, [x21, #144]
	ldr w9, [x19, #148]
	eor x9, x9, x15
	str w9, [x21, #148]
	ldr w9, [x19, #152]
	eor x9, x9, x15
	str w9, [x21, #152]
	ldr w9, [x19, #156]
	eor x9, x9, x15
	str w9, [x21, #156]
	ldr w9, [x19, #160]
	eor x9, x9, x15
	str w9, [x21, #160]
	ldr w9, [x19, #164]
	eor x9, x9, x15
	str w9, [x21, #164]
	ldr w9, [x19, #168]
	eor x9, x9, x15
	str w9, [x21, #168]
	ldr w9, [x19, #172]
	eor x9, x9, x15
	str w9, [x21, #172]
	ldr w9, [x19, #176]
	eor x9, x9, x15
	str w9, [x21, #176]
	ldr w9, [x19, #180]
	eor x9, x9, x15
	str w9, [x21, #180]
	ldr w9, [x19, #184]
	eor x9, x9, x15
	str w9, [x21, #184]
	ldr w9, [x19, #188]
	eor x9, x9, x15
	str w9, [x21, #188]
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	add x19, x21, #0
	add x1, x21, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.p2align 6

vg_hmac_sha384_finalize_scratch:
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #744
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch}
	ldp x9, x10, [x20, #0]
	stp x9, x10, [x19, #0]
	ldp x9, x10, [x20, #16]
	stp x9, x10, [x19, #16]
	ldp x9, x10, [x20, #32]
	stp x9, x10, [x19, #32]
	ldp x9, x10, [x20, #48]
	stp x9, x10, [x19, #48]
	ldr x9, [x23, #744]
	ldr x10, [x23, #752]
	stp x9, x10, [x19, #64]
	ldr x9, [x23, #760]
	ldr x10, [x23, #768]
	stp x9, x10, [x19, #80]
	ldr x9, [x23, #776]
	ldr x10, [x23, #784]
	stp x9, x10, [x19, #96]
	add x24, x21, #0
	add x21, x19, #64
	add x20, x23, #0
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x21, #48]
	stp x10, x10, [x21, #64]
	stp x10, x10, [x21, #80]
	stp x10, x10, [x21, #96]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldp x9, x10, [x21, #0]
	stp x9, x10, [x24, #0]
	ldp x9, x10, [x21, #16]
	stp x9, x10, [x24, #16]
	ldp x9, x10, [x21, #32]
	stp x9, x10, [x24, #32]
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.p2align 6

vg_hmac_sha384_init_sha3:
	.arch_extension sha3
	movz x10, #128, lsl #0
	movz x12, #0, lsl #0
	subs x11, x10, x3
	csel x9, x12, x3, hs
	cbnz x9, 20f
	sub sp, sp, #1872
	add x4, sp, #0
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha384_init}
	add x0, x21, #0
	bl {vg_sha384_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	str w14, [x19, #84]
	str w14, [x19, #88]
	str w14, [x19, #92]
	str w14, [x19, #96]
	str w14, [x19, #100]
	str w14, [x19, #104]
	str w14, [x19, #108]
	str w14, [x19, #112]
	str w14, [x19, #116]
	str w14, [x19, #120]
	str w14, [x19, #124]
	str w14, [x19, #128]
	str w14, [x19, #132]
	str w14, [x19, #136]
	str w14, [x19, #140]
	str w14, [x19, #144]
	str w14, [x19, #148]
	str w14, [x19, #152]
	str w14, [x19, #156]
	str w14, [x19, #160]
	str w14, [x19, #164]
	str w14, [x19, #168]
	str w14, [x19, #172]
	str w14, [x19, #176]
	str w14, [x19, #180]
	str w14, [x19, #184]
	str w14, [x19, #188]
	movz x10, #0, lsl #0
	cbz x24, 22f
24:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #64]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 24b
	b 23f
22:
23:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
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
	ldr w9, [x19, #84]
	eor x9, x9, x15
	str w9, [x21, #84]
	ldr w9, [x19, #88]
	eor x9, x9, x15
	str w9, [x21, #88]
	ldr w9, [x19, #92]
	eor x9, x9, x15
	str w9, [x21, #92]
	ldr w9, [x19, #96]
	eor x9, x9, x15
	str w9, [x21, #96]
	ldr w9, [x19, #100]
	eor x9, x9, x15
	str w9, [x21, #100]
	ldr w9, [x19, #104]
	eor x9, x9, x15
	str w9, [x21, #104]
	ldr w9, [x19, #108]
	eor x9, x9, x15
	str w9, [x21, #108]
	ldr w9, [x19, #112]
	eor x9, x9, x15
	str w9, [x21, #112]
	ldr w9, [x19, #116]
	eor x9, x9, x15
	str w9, [x21, #116]
	ldr w9, [x19, #120]
	eor x9, x9, x15
	str w9, [x21, #120]
	ldr w9, [x19, #124]
	eor x9, x9, x15
	str w9, [x21, #124]
	ldr w9, [x19, #128]
	eor x9, x9, x15
	str w9, [x21, #128]
	ldr w9, [x19, #132]
	eor x9, x9, x15
	str w9, [x21, #132]
	ldr w9, [x19, #136]
	eor x9, x9, x15
	str w9, [x21, #136]
	ldr w9, [x19, #140]
	eor x9, x9, x15
	str w9, [x21, #140]
	ldr w9, [x19, #144]
	eor x9, x9, x15
	str w9, [x21, #144]
	ldr w9, [x19, #148]
	eor x9, x9, x15
	str w9, [x21, #148]
	ldr w9, [x19, #152]
	eor x9, x9, x15
	str w9, [x21, #152]
	ldr w9, [x19, #156]
	eor x9, x9, x15
	str w9, [x21, #156]
	ldr w9, [x19, #160]
	eor x9, x9, x15
	str w9, [x21, #160]
	ldr w9, [x19, #164]
	eor x9, x9, x15
	str w9, [x21, #164]
	ldr w9, [x19, #168]
	eor x9, x9, x15
	str w9, [x21, #168]
	ldr w9, [x19, #172]
	eor x9, x9, x15
	str w9, [x21, #172]
	ldr w9, [x19, #176]
	eor x9, x9, x15
	str w9, [x21, #176]
	ldr w9, [x19, #180]
	eor x9, x9, x15
	str w9, [x21, #180]
	ldr w9, [x19, #184]
	eor x9, x9, x15
	str w9, [x21, #184]
	ldr w9, [x19, #188]
	eor x9, x9, x15
	str w9, [x21, #188]
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	add x19, x21, #0
	add x1, x21, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	add sp, sp, #1872
21:
	ret
20:
	sub sp, sp, #3408
	add x4, sp, #0
	str x19, [x4, #1872]
	str x20, [x4, #1880]
	str x21, [x4, #1888]
	str x22, [x4, #1896]
	str x24, [x4, #1904]
	str x30, [x4, #1912]
	str x23, [x4, #1920]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #7
	cbz x9, 25f
	sub x9, x20, #128
	cbz x9, 27f
	add x0, x23, #2528
	bl {vg_sha384_init}
	add x0, x23, #2528
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch_sha3}
	add x0, x23, #2528
	add x1, x20, #0
	add x2, x23, #2816
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha3}
	add x2, x23, #2816
	movz x3, #48, lsl #0
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
	bl {vg_hmac_sha384_init_scratch_sha3}
	ldr x19, [x23, #1872]
	ldr x20, [x23, #1880]
	ldr x21, [x23, #1888]
	ldr x22, [x23, #1896]
	ldr x24, [x23, #1904]
	ldr x30, [x23, #1912]
	ldr x23, [x23, #1920]
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3408
	b 21b
	.arch_extension nosha3
	.p2align 6

vg_hmac_sha384_finalize_sha3:
	.arch_extension sha3
	sub sp, sp, #1872
	add x4, sp, #0
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #744
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha3}
	ldp x9, x10, [x20, #0]
	stp x9, x10, [x19, #0]
	ldp x9, x10, [x20, #16]
	stp x9, x10, [x19, #16]
	ldp x9, x10, [x20, #32]
	stp x9, x10, [x19, #32]
	ldp x9, x10, [x20, #48]
	stp x9, x10, [x19, #48]
	ldr x9, [x23, #744]
	ldr x10, [x23, #752]
	stp x9, x10, [x19, #64]
	ldr x9, [x23, #760]
	ldr x10, [x23, #768]
	stp x9, x10, [x19, #80]
	ldr x9, [x23, #776]
	ldr x10, [x23, #784]
	stp x9, x10, [x19, #96]
	add x24, x21, #0
	add x21, x19, #64
	add x20, x23, #0
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x21, #48]
	stp x10, x10, [x21, #64]
	stp x10, x10, [x21, #80]
	stp x10, x10, [x21, #96]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldp x9, x10, [x21, #0]
	stp x9, x10, [x24, #0]
	ldp x9, x10, [x21, #16]
	stp x9, x10, [x24, #16]
	ldp x9, x10, [x21, #32]
	stp x9, x10, [x24, #32]
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	add sp, sp, #1872
	ret
	.arch_extension nosha3
	.p2align 6

vg_hmac_sha384_init_scratch_sha3:
	.arch_extension sha3
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha384_init}
	add x0, x21, #0
	bl {vg_sha384_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	str w14, [x19, #84]
	str w14, [x19, #88]
	str w14, [x19, #92]
	str w14, [x19, #96]
	str w14, [x19, #100]
	str w14, [x19, #104]
	str w14, [x19, #108]
	str w14, [x19, #112]
	str w14, [x19, #116]
	str w14, [x19, #120]
	str w14, [x19, #124]
	str w14, [x19, #128]
	str w14, [x19, #132]
	str w14, [x19, #136]
	str w14, [x19, #140]
	str w14, [x19, #144]
	str w14, [x19, #148]
	str w14, [x19, #152]
	str w14, [x19, #156]
	str w14, [x19, #160]
	str w14, [x19, #164]
	str w14, [x19, #168]
	str w14, [x19, #172]
	str w14, [x19, #176]
	str w14, [x19, #180]
	str w14, [x19, #184]
	str w14, [x19, #188]
	movz x10, #0, lsl #0
	cbz x24, 20f
22:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #64]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 22b
	b 21f
20:
21:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
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
	ldr w9, [x19, #84]
	eor x9, x9, x15
	str w9, [x21, #84]
	ldr w9, [x19, #88]
	eor x9, x9, x15
	str w9, [x21, #88]
	ldr w9, [x19, #92]
	eor x9, x9, x15
	str w9, [x21, #92]
	ldr w9, [x19, #96]
	eor x9, x9, x15
	str w9, [x21, #96]
	ldr w9, [x19, #100]
	eor x9, x9, x15
	str w9, [x21, #100]
	ldr w9, [x19, #104]
	eor x9, x9, x15
	str w9, [x21, #104]
	ldr w9, [x19, #108]
	eor x9, x9, x15
	str w9, [x21, #108]
	ldr w9, [x19, #112]
	eor x9, x9, x15
	str w9, [x21, #112]
	ldr w9, [x19, #116]
	eor x9, x9, x15
	str w9, [x21, #116]
	ldr w9, [x19, #120]
	eor x9, x9, x15
	str w9, [x21, #120]
	ldr w9, [x19, #124]
	eor x9, x9, x15
	str w9, [x21, #124]
	ldr w9, [x19, #128]
	eor x9, x9, x15
	str w9, [x21, #128]
	ldr w9, [x19, #132]
	eor x9, x9, x15
	str w9, [x21, #132]
	ldr w9, [x19, #136]
	eor x9, x9, x15
	str w9, [x21, #136]
	ldr w9, [x19, #140]
	eor x9, x9, x15
	str w9, [x21, #140]
	ldr w9, [x19, #144]
	eor x9, x9, x15
	str w9, [x21, #144]
	ldr w9, [x19, #148]
	eor x9, x9, x15
	str w9, [x21, #148]
	ldr w9, [x19, #152]
	eor x9, x9, x15
	str w9, [x21, #152]
	ldr w9, [x19, #156]
	eor x9, x9, x15
	str w9, [x21, #156]
	ldr w9, [x19, #160]
	eor x9, x9, x15
	str w9, [x21, #160]
	ldr w9, [x19, #164]
	eor x9, x9, x15
	str w9, [x21, #164]
	ldr w9, [x19, #168]
	eor x9, x9, x15
	str w9, [x21, #168]
	ldr w9, [x19, #172]
	eor x9, x9, x15
	str w9, [x21, #172]
	ldr w9, [x19, #176]
	eor x9, x9, x15
	str w9, [x21, #176]
	ldr w9, [x19, #180]
	eor x9, x9, x15
	str w9, [x21, #180]
	ldr w9, [x19, #184]
	eor x9, x9, x15
	str w9, [x21, #184]
	ldr w9, [x19, #188]
	eor x9, x9, x15
	str w9, [x21, #188]
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	add x19, x21, #0
	add x1, x21, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.arch_extension nosha3
	.p2align 6

vg_hmac_sha384_finalize_scratch_sha3:
	.arch_extension sha3
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #744
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha3}
	ldp x9, x10, [x20, #0]
	stp x9, x10, [x19, #0]
	ldp x9, x10, [x20, #16]
	stp x9, x10, [x19, #16]
	ldp x9, x10, [x20, #32]
	stp x9, x10, [x19, #32]
	ldp x9, x10, [x20, #48]
	stp x9, x10, [x19, #48]
	ldr x9, [x23, #744]
	ldr x10, [x23, #752]
	stp x9, x10, [x19, #64]
	ldr x9, [x23, #760]
	ldr x10, [x23, #768]
	stp x9, x10, [x19, #80]
	ldr x9, [x23, #776]
	ldr x10, [x23, #784]
	stp x9, x10, [x19, #96]
	add x24, x21, #0
	add x21, x19, #64
	add x20, x23, #0
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x21, #48]
	stp x10, x10, [x21, #64]
	stp x10, x10, [x21, #80]
	stp x10, x10, [x21, #96]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldp x9, x10, [x21, #0]
	stp x9, x10, [x24, #0]
	ldp x9, x10, [x21, #16]
	stp x9, x10, [x24, #16]
	ldp x9, x10, [x21, #32]
	stp x9, x10, [x24, #32]
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.arch_extension nosha3
	.p2align 6
