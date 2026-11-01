// The functions of `src/argon2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2:
	str x19, [sp, #-16]!
	str x20, [sp, #-16]!
	str x21, [sp, #-16]!
	str x22, [sp, #-16]!
	str x23, [sp, #-16]!
	str x24, [sp, #-16]!
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x19, sp, #0
	ldr x8, [sp, #384]
	str x8, [x19, #192]
	ldr x8, [sp, #392]
	str x8, [x19, #200]
	ldr x8, [sp, #400]
	str x8, [x19, #208]
	ldr x8, [sp, #408]
	str x8, [x19, #216]
	ldr x8, [sp, #416]
	str x8, [x19, #224]
	ldr x8, [sp, #424]
	str x8, [x19, #232]
	ldr x8, [sp, #432]
	str x8, [x19, #240]
	ldr x8, [sp, #440]
	str x8, [x19, #248]
	ldr x8, [sp, #448]
	str x8, [x19, #256]
	ldr x8, [sp, #456]
	str x8, [x19, #264]
	orr w0, w0, w0
	orr w5, w5, w5
	orr w6, w6, w6
	orr w7, w7, w7
	str x5, [x19, #72]
	str x4, [x19, #80]
	str x3, [x19, #88]
	str x2, [x19, #96]
	str x1, [x19, #104]
	str x0, [x19, #112]
	str x6, [x19, #176]
	str x7, [x19, #184]
	ldr x24, [x19, #248]
	ldr x8, [x19, #192]
	orr w8, w8, w8
	str x8, [x19, #192]
	ldr x0, [x19, #176]
	ldr x1, [x19, #184]
	add x1, x1, x1
	add x15, x1, #0
	add x1, x1, x1
	add x15, x1, #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x15, #32, lsl #0
20:
	lsr x3, x0, #31
	movz x9, #1, lsl #0
	and x3, x3, x9
	add x4, x4, x4
	add x4, x4, x3
	add x6, x4, #0
	sub x4, x4, x1
	lsr x8, x4, #63
	movz x9, #0, lsl #0
	sub x8, x9, x8
	eor x6, x6, x4
	and x6, x6, x8
	eor x4, x4, x6
	add x8, x8, #1
	add x5, x5, x5
	add x5, x5, x8
	add x0, x0, x0
	sub x15, x15, #1
	cbnz x15, 20b
	add x21, x5, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	movz x1, #64, lsl #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #832
	movz x3, #0, lsl #0
	bl {vg_blake2b_init}
	ldr x8, [x19, #184]
	str w8, [x24, #768]
	ldr x8, [x19, #264]
	str w8, [x24, #772]
	ldr x8, [x19, #176]
	str w8, [x24, #776]
	ldr x8, [x19, #72]
	str w8, [x24, #780]
	movz x8, #19, lsl #0
	str w8, [x24, #784]
	ldr x8, [x19, #112]
	str w8, [x24, #788]
	movz x1, #0, lsl #0
	add x2, x24, #0
	add x2, x2, #768
	movz x3, #24, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	movz x20, #24, lsl #0
	ldr x22, [x19, #96]
	str w22, [x24, #792]
	add x1, x20, #0
	add x2, x24, #0
	add x2, x2, #792
	add x15, x2, #0
	movz x3, #4, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, #4
	add x15, x20, #0
	add x1, x20, #0
	ldr x2, [x19, #104]
	add x3, x22, #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, x22
	add x15, x20, #0
	ldr x22, [x19, #80]
	str w22, [x24, #792]
	add x1, x20, #0
	add x2, x24, #0
	add x2, x2, #792
	add x15, x2, #0
	movz x3, #4, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, #4
	add x15, x20, #0
	add x1, x20, #0
	ldr x2, [x19, #88]
	add x3, x22, #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, x22
	add x15, x20, #0
	ldr x22, [x19, #208]
	str w22, [x24, #792]
	add x1, x20, #0
	add x2, x24, #0
	add x2, x2, #792
	add x15, x2, #0
	movz x3, #4, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, #4
	add x15, x20, #0
	add x1, x20, #0
	ldr x2, [x19, #200]
	add x3, x22, #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, x22
	add x15, x20, #0
	ldr x22, [x19, #224]
	str w22, [x24, #792]
	add x1, x20, #0
	add x2, x24, #0
	add x2, x2, #792
	add x15, x2, #0
	movz x3, #4, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, #4
	add x15, x20, #0
	add x1, x20, #0
	ldr x2, [x19, #216]
	add x3, x22, #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x20, x20, x22
	add x15, x20, #0
	add x1, x20, #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #768
	add x3, x24, #0
	add x3, x3, #192
	bl {vg_blake2b_finalize_scratch}
	add x22, x19, #0
	movz x8, #64, lsl #0
	add x2, x24, #0
	add x2, x2, #768
21:
	ldrb w3, [x2, #0]
	strb w3, [x22, #0]
	add x2, x2, #1
	add x22, x22, #1
	sub x8, x8, #1
	cbnz x8, 21b
	ldr x22, [x19, #232]
	ldr x8, [x19, #240]
	movz x3, #0, lsl #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
22:
	str x3, [x22, #0]
	add x22, x22, #8
	add x15, x22, #0
	movz x12, #1, lsl #0
	subs x8, x8, x12
	add x15, x8, #0
	cbnz x15, 22b
	ldr x22, [x19, #232]
	movz x20, #0, lsl #0
	ldr x23, [x19, #184]
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
	add x21, x21, x21
	add x15, x21, #0
23:
	movz x8, #0, lsl #0
	str w8, [x19, #64]
	str w20, [x19, #68]
	add x0, x19, #0
	movz x1, #72, lsl #0
	add x2, x22, #0
	movz x3, #1024, lsl #0
	add x4, x24, #0
	bl {vg_argon2_hprime}
	add x22, x22, #1024
	add x15, x22, #0
	movz x8, #1, lsl #0
	str w8, [x19, #64]
	str w20, [x19, #68]
	add x0, x19, #0
	movz x1, #72, lsl #0
	add x2, x22, #0
	movz x3, #1024, lsl #0
	add x4, x24, #0
	bl {vg_argon2_hprime}
	add x22, x22, x21
	add x15, x22, #0
	movz x12, #1024, lsl #0
	subs x22, x22, x12
	add x15, x22, #0
	add x20, x20, #1
	add x15, x20, #0
	movz x12, #1, lsl #0
	subs x23, x23, x12
	add x15, x23, #0
	cbnz x15, 23b
	add x20, x21, #0
	lsr x20, x20, #10
	add x15, x20, #0
	lsr x21, x21, #12
	add x15, x21, #0
	movz x8, #0, lsl #0
	str x8, [x19, #0]
	movz x24, #0, lsl #0
	movz x22, #0, lsl #0
24:
	movz x22, #0, lsl #0
25:
	movz x24, #0, lsl #0
26:
	movz x8, #0, lsl #0
	str x8, [x19, #8]
	ldr x3, [x19, #0]
	orr x3, x3, x22
	add x15, x3, #0
	movz x13, #0, lsl #0
	subs x15, x3, x13
	lsr x14, x15, #63
	cbz x15, 27f
	movz x23, #0, lsl #0
	b 28f
27:
	movz x23, #2, lsl #0
28:
	subs x15, x23, x21
	lsr x14, x15, #63
	cbnz x14, 29f
	b 210f
29:
211:
	ldr x8, [x19, #112]
	add x6, x8, #0
	movz x12, #1, lsl #0
	eor x6, x6, x12
	add x15, x6, #0
	movz x13, #1, lsl #0
	subs x15, x6, x13
	lsr x14, x15, #63
	sbcs x6, x6, x6
	add x15, x6, #0
	add x4, x8, #0
	movz x12, #2, lsl #0
	eor x4, x4, x12
	add x15, x4, #0
	movz x13, #1, lsl #0
	subs x15, x4, x13
	lsr x14, x15, #63
	sbcs x4, x4, x4
	add x15, x4, #0
	ldr x5, [x19, #0]
	movz x13, #1, lsl #0
	subs x15, x5, x13
	lsr x14, x15, #63
	sbcs x5, x5, x5
	add x15, x5, #0
	movz x13, #2, lsl #0
	subs x15, x22, x13
	lsr x14, x15, #63
	sbcs x7, x7, x7
	add x15, x7, #0
	and x4, x4, x5
	add x15, x4, #0
	and x4, x4, x7
	add x15, x4, #0
	orr x6, x6, x4
	add x15, x6, #0
	movz x12, #1, lsl #0
	and x6, x6, x12
	add x15, x6, #0
	movz x13, #0, lsl #0
	subs x15, x6, x13
	lsr x14, x15, #63
	cbz x15, 212f
	add x8, x23, #0
	lsr x8, x8, #7
	add x15, x8, #0
	add x8, x8, #1
	add x15, x8, #0
	ldr x13, [x19, #8]
	subs x15, x8, x13
	lsr x14, x15, #63
	cbz x15, 214f
	str x8, [x19, #8]
	ldr x0, [x19, #248]
	movz x12, #5120, lsl #0
	add x0, x0, x12
	add x15, x0, #0
	movz x8, #0, lsl #0
	str x8, [x0, #0]
	str x8, [x0, #8]
	str x8, [x0, #16]
	str x8, [x0, #24]
	str x8, [x0, #32]
	str x8, [x0, #40]
	str x8, [x0, #48]
	str x8, [x0, #56]
	str x8, [x0, #64]
	str x8, [x0, #72]
	str x8, [x0, #80]
	str x8, [x0, #88]
	str x8, [x0, #96]
	str x8, [x0, #104]
	str x8, [x0, #112]
	str x8, [x0, #120]
	str x8, [x0, #128]
	str x8, [x0, #136]
	str x8, [x0, #144]
	str x8, [x0, #152]
	str x8, [x0, #160]
	str x8, [x0, #168]
	str x8, [x0, #176]
	str x8, [x0, #184]
	str x8, [x0, #192]
	str x8, [x0, #200]
	str x8, [x0, #208]
	str x8, [x0, #216]
	str x8, [x0, #224]
	str x8, [x0, #232]
	str x8, [x0, #240]
	str x8, [x0, #248]
	str x8, [x0, #256]
	str x8, [x0, #264]
	str x8, [x0, #272]
	str x8, [x0, #280]
	str x8, [x0, #288]
	str x8, [x0, #296]
	str x8, [x0, #304]
	str x8, [x0, #312]
	str x8, [x0, #320]
	str x8, [x0, #328]
	str x8, [x0, #336]
	str x8, [x0, #344]
	str x8, [x0, #352]
	str x8, [x0, #360]
	str x8, [x0, #368]
	str x8, [x0, #376]
	str x8, [x0, #384]
	str x8, [x0, #392]
	str x8, [x0, #400]
	str x8, [x0, #408]
	str x8, [x0, #416]
	str x8, [x0, #424]
	str x8, [x0, #432]
	str x8, [x0, #440]
	str x8, [x0, #448]
	str x8, [x0, #456]
	str x8, [x0, #464]
	str x8, [x0, #472]
	str x8, [x0, #480]
	str x8, [x0, #488]
	str x8, [x0, #496]
	str x8, [x0, #504]
	str x8, [x0, #512]
	str x8, [x0, #520]
	str x8, [x0, #528]
	str x8, [x0, #536]
	str x8, [x0, #544]
	str x8, [x0, #552]
	str x8, [x0, #560]
	str x8, [x0, #568]
	str x8, [x0, #576]
	str x8, [x0, #584]
	str x8, [x0, #592]
	str x8, [x0, #600]
	str x8, [x0, #608]
	str x8, [x0, #616]
	str x8, [x0, #624]
	str x8, [x0, #632]
	str x8, [x0, #640]
	str x8, [x0, #648]
	str x8, [x0, #656]
	str x8, [x0, #664]
	str x8, [x0, #672]
	str x8, [x0, #680]
	str x8, [x0, #688]
	str x8, [x0, #696]
	str x8, [x0, #704]
	str x8, [x0, #712]
	str x8, [x0, #720]
	str x8, [x0, #728]
	str x8, [x0, #736]
	str x8, [x0, #744]
	str x8, [x0, #752]
	str x8, [x0, #760]
	str x8, [x0, #768]
	str x8, [x0, #776]
	str x8, [x0, #784]
	str x8, [x0, #792]
	str x8, [x0, #800]
	str x8, [x0, #808]
	str x8, [x0, #816]
	str x8, [x0, #824]
	str x8, [x0, #832]
	str x8, [x0, #840]
	str x8, [x0, #848]
	str x8, [x0, #856]
	str x8, [x0, #864]
	str x8, [x0, #872]
	str x8, [x0, #880]
	str x8, [x0, #888]
	str x8, [x0, #896]
	str x8, [x0, #904]
	str x8, [x0, #912]
	str x8, [x0, #920]
	str x8, [x0, #928]
	str x8, [x0, #936]
	str x8, [x0, #944]
	str x8, [x0, #952]
	str x8, [x0, #960]
	str x8, [x0, #968]
	str x8, [x0, #976]
	str x8, [x0, #984]
	str x8, [x0, #992]
	str x8, [x0, #1000]
	str x8, [x0, #1008]
	str x8, [x0, #1016]
	ldr x0, [x19, #248]
	movz x12, #7168, lsl #0
	add x0, x0, x12
	add x15, x0, #0
	movz x8, #0, lsl #0
	str x8, [x0, #0]
	str x8, [x0, #8]
	str x8, [x0, #16]
	str x8, [x0, #24]
	str x8, [x0, #32]
	str x8, [x0, #40]
	str x8, [x0, #48]
	str x8, [x0, #56]
	str x8, [x0, #64]
	str x8, [x0, #72]
	str x8, [x0, #80]
	str x8, [x0, #88]
	str x8, [x0, #96]
	str x8, [x0, #104]
	str x8, [x0, #112]
	str x8, [x0, #120]
	str x8, [x0, #128]
	str x8, [x0, #136]
	str x8, [x0, #144]
	str x8, [x0, #152]
	str x8, [x0, #160]
	str x8, [x0, #168]
	str x8, [x0, #176]
	str x8, [x0, #184]
	str x8, [x0, #192]
	str x8, [x0, #200]
	str x8, [x0, #208]
	str x8, [x0, #216]
	str x8, [x0, #224]
	str x8, [x0, #232]
	str x8, [x0, #240]
	str x8, [x0, #248]
	str x8, [x0, #256]
	str x8, [x0, #264]
	str x8, [x0, #272]
	str x8, [x0, #280]
	str x8, [x0, #288]
	str x8, [x0, #296]
	str x8, [x0, #304]
	str x8, [x0, #312]
	str x8, [x0, #320]
	str x8, [x0, #328]
	str x8, [x0, #336]
	str x8, [x0, #344]
	str x8, [x0, #352]
	str x8, [x0, #360]
	str x8, [x0, #368]
	str x8, [x0, #376]
	str x8, [x0, #384]
	str x8, [x0, #392]
	str x8, [x0, #400]
	str x8, [x0, #408]
	str x8, [x0, #416]
	str x8, [x0, #424]
	str x8, [x0, #432]
	str x8, [x0, #440]
	str x8, [x0, #448]
	str x8, [x0, #456]
	str x8, [x0, #464]
	str x8, [x0, #472]
	str x8, [x0, #480]
	str x8, [x0, #488]
	str x8, [x0, #496]
	str x8, [x0, #504]
	str x8, [x0, #512]
	str x8, [x0, #520]
	str x8, [x0, #528]
	str x8, [x0, #536]
	str x8, [x0, #544]
	str x8, [x0, #552]
	str x8, [x0, #560]
	str x8, [x0, #568]
	str x8, [x0, #576]
	str x8, [x0, #584]
	str x8, [x0, #592]
	str x8, [x0, #600]
	str x8, [x0, #608]
	str x8, [x0, #616]
	str x8, [x0, #624]
	str x8, [x0, #632]
	str x8, [x0, #640]
	str x8, [x0, #648]
	str x8, [x0, #656]
	str x8, [x0, #664]
	str x8, [x0, #672]
	str x8, [x0, #680]
	str x8, [x0, #688]
	str x8, [x0, #696]
	str x8, [x0, #704]
	str x8, [x0, #712]
	str x8, [x0, #720]
	str x8, [x0, #728]
	str x8, [x0, #736]
	str x8, [x0, #744]
	str x8, [x0, #752]
	str x8, [x0, #760]
	str x8, [x0, #768]
	str x8, [x0, #776]
	str x8, [x0, #784]
	str x8, [x0, #792]
	str x8, [x0, #800]
	str x8, [x0, #808]
	str x8, [x0, #816]
	str x8, [x0, #824]
	str x8, [x0, #832]
	str x8, [x0, #840]
	str x8, [x0, #848]
	str x8, [x0, #856]
	str x8, [x0, #864]
	str x8, [x0, #872]
	str x8, [x0, #880]
	str x8, [x0, #888]
	str x8, [x0, #896]
	str x8, [x0, #904]
	str x8, [x0, #912]
	str x8, [x0, #920]
	str x8, [x0, #928]
	str x8, [x0, #936]
	str x8, [x0, #944]
	str x8, [x0, #952]
	str x8, [x0, #960]
	str x8, [x0, #968]
	str x8, [x0, #976]
	str x8, [x0, #984]
	str x8, [x0, #992]
	str x8, [x0, #1000]
	str x8, [x0, #1008]
	str x8, [x0, #1016]
	ldr x0, [x19, #248]
	movz x12, #5120, lsl #0
	add x0, x0, x12
	add x15, x0, #0
	ldr x8, [x19, #0]
	str x8, [x0, #0]
	str x24, [x0, #8]
	str x22, [x0, #16]
	ldr x8, [x19, #240]
	str x8, [x0, #24]
	ldr x8, [x19, #72]
	str x8, [x0, #32]
	ldr x8, [x19, #112]
	str x8, [x0, #40]
	ldr x8, [x19, #8]
	str x8, [x0, #48]
	ldr x3, [x19, #248]
	add x0, x3, #0
	movz x12, #7168, lsl #0
	add x0, x0, x12
	add x15, x0, #0
	add x1, x3, #0
	movz x12, #5120, lsl #0
	add x1, x1, x12
	add x15, x1, #0
	add x2, x3, #0
	movz x12, #4096, lsl #0
	add x2, x2, x12
	add x15, x2, #0
	bl {vg_argon2_compress}
	ldr x3, [x19, #248]
	add x0, x3, #0
	movz x12, #7168, lsl #0
	add x0, x0, x12
	add x15, x0, #0
	add x1, x3, #0
	movz x12, #4096, lsl #0
	add x1, x1, x12
	add x15, x1, #0
	add x2, x3, #0
	movz x12, #6144, lsl #0
	add x2, x2, x12
	add x15, x2, #0
	bl {vg_argon2_compress}
	b 215f
214:
215:
	ldr x3, [x19, #248]
	add x8, x23, #0
	movz x12, #127, lsl #0
	and x8, x8, x12
	add x15, x8, #0
	add x13, x8, #0
	add x13, x13, x13
	add x15, x13, #0
	add x13, x13, x13
	add x15, x13, #0
	add x13, x13, x13
	add x15, x13, #0
	add x13, x13, x3
	add x15, x13, #0
	movz x12, #6144, lsl #0
	add x13, x13, x12
	add x15, x13, #0
	ldr x0, [x13, #0]
	b 213f
212:
	ldr x4, [x19, #232]
	add x8, x22, #0
	umulh x2, x8, x21
	mul x8, x8, x21
	add x3, x8, #0
	add x3, x3, x23
	add x15, x3, #0
	movz x13, #0, lsl #0
	subs x15, x3, x13
	lsr x14, x15, #63
	cbz x15, 216f
	add x0, x3, #0
	b 217f
216:
	add x0, x20, #0
217:
	movz x12, #1, lsl #0
	subs x0, x0, x12
	add x15, x0, #0
	add x3, x0, #0
	add x8, x24, #0
	umulh x2, x8, x20
	mul x8, x8, x20
	add x8, x8, x3
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x4
	add x15, x8, #0
	ldr x0, [x8, #0]
213:
	ldr x1, [x19, #184]
	add x7, x0, #0
	lsr x0, x0, #32
	add x15, x0, #0
	movz x4, #0, lsl #0
	lsl x0, x0, #32
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	extr x4, x4, x0, #63
	lsl x0, x0, #1
	subs x9, x4, x1
	csel x4, x9, x4, hs
	ldr x5, [x19, #0]
	add x8, x5, #0
	orr x8, x8, x22
	add x15, x8, #0
	cbz x15, 218f
	b 219f
218:
	add x4, x24, #0
219:
	add x0, x4, #0
	add x1, x24, #0
	movz x13, #0, lsl #0
	subs x15, x5, x13
	lsr x14, x15, #63
	cbz x15, 220f
	add x8, x22, #0
	add x8, x8, #1
	add x15, x8, #0
	umulh x2, x8, x21
	mul x8, x8, x21
	add x6, x8, #0
	movz x13, #3, lsl #0
	subs x15, x22, x13
	lsr x14, x15, #63
	cbz x15, 222f
	b 223f
222:
	movz x6, #0, lsl #0
223:
	b 221f
220:
	movz x6, #0, lsl #0
221:
	movz x13, #0, lsl #0
	subs x15, x5, x13
	lsr x14, x15, #63
	cbz x15, 224f
	add x8, x20, #0
	subs x8, x8, x21
	add x15, x8, #0
	add x3, x8, #0
	add x2, x8, #0
	add x2, x2, x23
	add x15, x2, #0
	movz x12, #1, lsl #0
	subs x2, x2, x12
	add x15, x2, #0
	b 225f
224:
	add x8, x21, #0
	umulh x2, x8, x22
	mul x8, x8, x22
	add x3, x8, #0
	add x2, x8, #0
	add x2, x2, x23
	add x15, x2, #0
	movz x12, #1, lsl #0
	subs x2, x2, x12
	add x15, x2, #0
225:
	add x4, x23, #0
	movz x12, #1, lsl #0
	subs x4, x4, x12
	add x15, x4, #0
	sbcs x5, x5, x5
	add x15, x5, #0
	add x3, x3, x5
	add x15, x3, #0
	add x8, x0, #0
	eor x8, x8, x1
	add x15, x8, #0
	movz x12, #1, lsl #0
	subs x8, x8, x12
	add x15, x8, #0
	sbcs x8, x8, x8
	add x15, x8, #0
	add x4, x3, #0
	eor x2, x2, x3
	add x15, x2, #0
	and x2, x2, x8
	add x15, x2, #0
	eor x4, x4, x2
	add x15, x4, #0
	add x5, x0, #0
	add x0, x7, #0
	add x1, x4, #0
	orr w8, w0, w0
	umulh x2, x8, x8
	mul x8, x8, x8
	lsr x8, x8, #32
	add x15, x8, #0
	umulh x2, x8, x1
	mul x8, x8, x1
	lsr x8, x8, #32
	add x15, x8, #0
	add x3, x1, #0
	movz x12, #1, lsl #0
	subs x3, x3, x12
	add x15, x3, #0
	subs x3, x3, x8
	add x15, x3, #0
	add x8, x3, #0
	add x0, x8, #0
	add x0, x0, x6
	add x15, x0, #0
	add x1, x20, #0
	add x6, x0, #0
	subs x0, x0, x1
	add x15, x0, #0
	sbcs x8, x8, x8
	add x15, x8, #0
	eor x6, x6, x0
	add x15, x6, #0
	and x6, x6, x8
	add x15, x6, #0
	eor x0, x0, x6
	add x15, x0, #0
	ldr x4, [x19, #232]
	add x1, x0, #0
	add x8, x22, #0
	umulh x2, x8, x21
	mul x8, x8, x21
	add x3, x8, #0
	add x3, x3, x23
	add x15, x3, #0
	movz x13, #0, lsl #0
	subs x15, x3, x13
	lsr x14, x15, #63
	cbz x15, 226f
	add x0, x3, #0
	b 227f
226:
	add x0, x20, #0
227:
	movz x12, #1, lsl #0
	subs x0, x0, x12
	add x15, x0, #0
	add x8, x24, #0
	umulh x2, x8, x20
	mul x8, x8, x20
	add x8, x8, x3
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x4
	add x15, x8, #0
	add x6, x8, #0
	add x3, x0, #0
	add x8, x24, #0
	umulh x2, x8, x20
	mul x8, x8, x20
	add x8, x8, x3
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x4
	add x15, x8, #0
	add x7, x8, #0
	add x3, x1, #0
	add x8, x5, #0
	umulh x2, x8, x20
	mul x8, x8, x20
	add x8, x8, x3
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x4
	add x15, x8, #0
	add x1, x8, #0
	add x0, x7, #0
	str x6, [x19, #16]
	ldr x3, [x19, #248]
	add x2, x3, #0
	movz x12, #4096, lsl #0
	add x2, x2, x12
	add x15, x2, #0
	bl {vg_argon2_compress}
	ldr x0, [x19, #16]
	ldr x1, [x19, #248]
	movz x12, #4096, lsl #0
	add x1, x1, x12
	add x15, x1, #0
	ldr x5, [x19, #0]
	movz x13, #0, lsl #0
	subs x15, x5, x13
	lsr x14, x15, #63
	cbz x15, 228f
	ldr q0, [x1, #0]
	ldr q1, [x0, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #0]
	ldr q0, [x1, #16]
	ldr q1, [x0, #16]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #16]
	ldr q0, [x1, #32]
	ldr q1, [x0, #32]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #32]
	ldr q0, [x1, #48]
	ldr q1, [x0, #48]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #48]
	ldr q0, [x1, #64]
	ldr q1, [x0, #64]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #64]
	ldr q0, [x1, #80]
	ldr q1, [x0, #80]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #80]
	ldr q0, [x1, #96]
	ldr q1, [x0, #96]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #96]
	ldr q0, [x1, #112]
	ldr q1, [x0, #112]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #112]
	ldr q0, [x1, #128]
	ldr q1, [x0, #128]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #128]
	ldr q0, [x1, #144]
	ldr q1, [x0, #144]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #144]
	ldr q0, [x1, #160]
	ldr q1, [x0, #160]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #160]
	ldr q0, [x1, #176]
	ldr q1, [x0, #176]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #176]
	ldr q0, [x1, #192]
	ldr q1, [x0, #192]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #192]
	ldr q0, [x1, #208]
	ldr q1, [x0, #208]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #208]
	ldr q0, [x1, #224]
	ldr q1, [x0, #224]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #224]
	ldr q0, [x1, #240]
	ldr q1, [x0, #240]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #240]
	ldr q0, [x1, #256]
	ldr q1, [x0, #256]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #256]
	ldr q0, [x1, #272]
	ldr q1, [x0, #272]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #272]
	ldr q0, [x1, #288]
	ldr q1, [x0, #288]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #288]
	ldr q0, [x1, #304]
	ldr q1, [x0, #304]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #304]
	ldr q0, [x1, #320]
	ldr q1, [x0, #320]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #320]
	ldr q0, [x1, #336]
	ldr q1, [x0, #336]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #336]
	ldr q0, [x1, #352]
	ldr q1, [x0, #352]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #352]
	ldr q0, [x1, #368]
	ldr q1, [x0, #368]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #368]
	ldr q0, [x1, #384]
	ldr q1, [x0, #384]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #384]
	ldr q0, [x1, #400]
	ldr q1, [x0, #400]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #400]
	ldr q0, [x1, #416]
	ldr q1, [x0, #416]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #416]
	ldr q0, [x1, #432]
	ldr q1, [x0, #432]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #432]
	ldr q0, [x1, #448]
	ldr q1, [x0, #448]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #448]
	ldr q0, [x1, #464]
	ldr q1, [x0, #464]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #464]
	ldr q0, [x1, #480]
	ldr q1, [x0, #480]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #480]
	ldr q0, [x1, #496]
	ldr q1, [x0, #496]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #496]
	ldr q0, [x1, #512]
	ldr q1, [x0, #512]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #512]
	ldr q0, [x1, #528]
	ldr q1, [x0, #528]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #528]
	ldr q0, [x1, #544]
	ldr q1, [x0, #544]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #544]
	ldr q0, [x1, #560]
	ldr q1, [x0, #560]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #560]
	ldr q0, [x1, #576]
	ldr q1, [x0, #576]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #576]
	ldr q0, [x1, #592]
	ldr q1, [x0, #592]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #592]
	ldr q0, [x1, #608]
	ldr q1, [x0, #608]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #608]
	ldr q0, [x1, #624]
	ldr q1, [x0, #624]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #624]
	ldr q0, [x1, #640]
	ldr q1, [x0, #640]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #640]
	ldr q0, [x1, #656]
	ldr q1, [x0, #656]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #656]
	ldr q0, [x1, #672]
	ldr q1, [x0, #672]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #672]
	ldr q0, [x1, #688]
	ldr q1, [x0, #688]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #688]
	ldr q0, [x1, #704]
	ldr q1, [x0, #704]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #704]
	ldr q0, [x1, #720]
	ldr q1, [x0, #720]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #720]
	ldr q0, [x1, #736]
	ldr q1, [x0, #736]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #736]
	ldr q0, [x1, #752]
	ldr q1, [x0, #752]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #752]
	ldr q0, [x1, #768]
	ldr q1, [x0, #768]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #768]
	ldr q0, [x1, #784]
	ldr q1, [x0, #784]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #784]
	ldr q0, [x1, #800]
	ldr q1, [x0, #800]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #800]
	ldr q0, [x1, #816]
	ldr q1, [x0, #816]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #816]
	ldr q0, [x1, #832]
	ldr q1, [x0, #832]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #832]
	ldr q0, [x1, #848]
	ldr q1, [x0, #848]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #848]
	ldr q0, [x1, #864]
	ldr q1, [x0, #864]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #864]
	ldr q0, [x1, #880]
	ldr q1, [x0, #880]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #880]
	ldr q0, [x1, #896]
	ldr q1, [x0, #896]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #896]
	ldr q0, [x1, #912]
	ldr q1, [x0, #912]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #912]
	ldr q0, [x1, #928]
	ldr q1, [x0, #928]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #928]
	ldr q0, [x1, #944]
	ldr q1, [x0, #944]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #944]
	ldr q0, [x1, #960]
	ldr q1, [x0, #960]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #960]
	ldr q0, [x1, #976]
	ldr q1, [x0, #976]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #976]
	ldr q0, [x1, #992]
	ldr q1, [x0, #992]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #992]
	ldr q0, [x1, #1008]
	ldr q1, [x0, #1008]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x0, #1008]
	b 229f
228:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	ldr q0, [x1, #16]
	str q0, [x0, #16]
	ldr q0, [x1, #32]
	str q0, [x0, #32]
	ldr q0, [x1, #48]
	str q0, [x0, #48]
	ldr q0, [x1, #64]
	str q0, [x0, #64]
	ldr q0, [x1, #80]
	str q0, [x0, #80]
	ldr q0, [x1, #96]
	str q0, [x0, #96]
	ldr q0, [x1, #112]
	str q0, [x0, #112]
	ldr q0, [x1, #128]
	str q0, [x0, #128]
	ldr q0, [x1, #144]
	str q0, [x0, #144]
	ldr q0, [x1, #160]
	str q0, [x0, #160]
	ldr q0, [x1, #176]
	str q0, [x0, #176]
	ldr q0, [x1, #192]
	str q0, [x0, #192]
	ldr q0, [x1, #208]
	str q0, [x0, #208]
	ldr q0, [x1, #224]
	str q0, [x0, #224]
	ldr q0, [x1, #240]
	str q0, [x0, #240]
	ldr q0, [x1, #256]
	str q0, [x0, #256]
	ldr q0, [x1, #272]
	str q0, [x0, #272]
	ldr q0, [x1, #288]
	str q0, [x0, #288]
	ldr q0, [x1, #304]
	str q0, [x0, #304]
	ldr q0, [x1, #320]
	str q0, [x0, #320]
	ldr q0, [x1, #336]
	str q0, [x0, #336]
	ldr q0, [x1, #352]
	str q0, [x0, #352]
	ldr q0, [x1, #368]
	str q0, [x0, #368]
	ldr q0, [x1, #384]
	str q0, [x0, #384]
	ldr q0, [x1, #400]
	str q0, [x0, #400]
	ldr q0, [x1, #416]
	str q0, [x0, #416]
	ldr q0, [x1, #432]
	str q0, [x0, #432]
	ldr q0, [x1, #448]
	str q0, [x0, #448]
	ldr q0, [x1, #464]
	str q0, [x0, #464]
	ldr q0, [x1, #480]
	str q0, [x0, #480]
	ldr q0, [x1, #496]
	str q0, [x0, #496]
	ldr q0, [x1, #512]
	str q0, [x0, #512]
	ldr q0, [x1, #528]
	str q0, [x0, #528]
	ldr q0, [x1, #544]
	str q0, [x0, #544]
	ldr q0, [x1, #560]
	str q0, [x0, #560]
	ldr q0, [x1, #576]
	str q0, [x0, #576]
	ldr q0, [x1, #592]
	str q0, [x0, #592]
	ldr q0, [x1, #608]
	str q0, [x0, #608]
	ldr q0, [x1, #624]
	str q0, [x0, #624]
	ldr q0, [x1, #640]
	str q0, [x0, #640]
	ldr q0, [x1, #656]
	str q0, [x0, #656]
	ldr q0, [x1, #672]
	str q0, [x0, #672]
	ldr q0, [x1, #688]
	str q0, [x0, #688]
	ldr q0, [x1, #704]
	str q0, [x0, #704]
	ldr q0, [x1, #720]
	str q0, [x0, #720]
	ldr q0, [x1, #736]
	str q0, [x0, #736]
	ldr q0, [x1, #752]
	str q0, [x0, #752]
	ldr q0, [x1, #768]
	str q0, [x0, #768]
	ldr q0, [x1, #784]
	str q0, [x0, #784]
	ldr q0, [x1, #800]
	str q0, [x0, #800]
	ldr q0, [x1, #816]
	str q0, [x0, #816]
	ldr q0, [x1, #832]
	str q0, [x0, #832]
	ldr q0, [x1, #848]
	str q0, [x0, #848]
	ldr q0, [x1, #864]
	str q0, [x0, #864]
	ldr q0, [x1, #880]
	str q0, [x0, #880]
	ldr q0, [x1, #896]
	str q0, [x0, #896]
	ldr q0, [x1, #912]
	str q0, [x0, #912]
	ldr q0, [x1, #928]
	str q0, [x0, #928]
	ldr q0, [x1, #944]
	str q0, [x0, #944]
	ldr q0, [x1, #960]
	str q0, [x0, #960]
	ldr q0, [x1, #976]
	str q0, [x0, #976]
	ldr q0, [x1, #992]
	str q0, [x0, #992]
	ldr q0, [x1, #1008]
	str q0, [x0, #1008]
229:
	add x23, x23, #1
	add x15, x23, #0
	subs x15, x23, x21
	lsr x14, x15, #63
	cbnz x14, 211b
210:
	add x24, x24, #1
	add x15, x24, #0
	ldr x13, [x19, #184]
	subs x15, x24, x13
	lsr x14, x15, #63
	cbnz x14, 26b
	add x22, x22, #1
	add x15, x22, #0
	movz x13, #4, lsl #0
	subs x15, x22, x13
	lsr x14, x15, #63
	cbnz x14, 25b
	ldr x8, [x19, #0]
	add x8, x8, #1
	add x15, x8, #0
	str x8, [x19, #0]
	ldr x13, [x19, #72]
	subs x15, x8, x13
	lsr x14, x15, #63
	cbnz x14, 24b
	ldr x0, [x19, #232]
	movz x24, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #8, lsl #0
230:
	str x8, [x0, #0]
	str x8, [x0, #8]
	str x8, [x0, #16]
	str x8, [x0, #24]
	str x8, [x0, #32]
	str x8, [x0, #40]
	str x8, [x0, #48]
	str x8, [x0, #56]
	str x8, [x0, #64]
	str x8, [x0, #72]
	str x8, [x0, #80]
	str x8, [x0, #88]
	str x8, [x0, #96]
	str x8, [x0, #104]
	str x8, [x0, #112]
	str x8, [x0, #120]
	add x0, x0, #128
	sub x9, x9, #1
	cbnz x9, 230b
	sub x0, x0, #1024
231:
	ldr x4, [x19, #232]
	add x8, x24, #0
	add x3, x20, #0
	movz x12, #1, lsl #0
	subs x3, x3, x12
	add x15, x3, #0
	umulh x2, x8, x20
	mul x8, x8, x20
	add x8, x8, x3
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x8
	add x15, x8, #0
	add x8, x8, x4
	add x15, x8, #0
	add x1, x8, #0
	add x0, x4, #0
	movz x14, #16, lsl #0
232:
	ldr x8, [x1, #0]
	ldr x13, [x0, #0]
	eor x8, x8, x13
	str x8, [x0, #0]
	ldr x8, [x1, #8]
	ldr x13, [x0, #8]
	eor x8, x8, x13
	str x8, [x0, #8]
	ldr x8, [x1, #16]
	ldr x13, [x0, #16]
	eor x8, x8, x13
	str x8, [x0, #16]
	ldr x8, [x1, #24]
	ldr x13, [x0, #24]
	eor x8, x8, x13
	str x8, [x0, #24]
	ldr x8, [x1, #32]
	ldr x13, [x0, #32]
	eor x8, x8, x13
	str x8, [x0, #32]
	ldr x8, [x1, #40]
	ldr x13, [x0, #40]
	eor x8, x8, x13
	str x8, [x0, #40]
	ldr x8, [x1, #48]
	ldr x13, [x0, #48]
	eor x8, x8, x13
	str x8, [x0, #48]
	ldr x8, [x1, #56]
	ldr x13, [x0, #56]
	eor x8, x8, x13
	str x8, [x0, #56]
	add x0, x0, #64
	add x1, x1, #64
	sub x14, x14, #1
	cbnz x14, 232b
	sub x0, x0, #1024
	sub x1, x1, #1024
	add x24, x24, #1
	add x15, x24, #0
	ldr x13, [x19, #184]
	subs x15, x24, x13
	lsr x14, x15, #63
	cbnz x14, 231b
	ldr x0, [x19, #232]
	movz x1, #1024, lsl #0
	ldr x2, [x19, #256]
	ldr x3, [x19, #264]
	ldr x4, [x19, #248]
	bl {vg_argon2_hprime}
	add sp, sp, #272
	ldr x30, [sp], #16
	ldr x24, [sp], #16
	ldr x23, [sp], #16
	ldr x22, [sp], #16
	ldr x21, [sp], #16
	ldr x20, [sp], #16
	ldr x19, [sp], #16
	ret
	.p2align 6
