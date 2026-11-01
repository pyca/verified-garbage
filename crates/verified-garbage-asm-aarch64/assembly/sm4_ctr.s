// The functions of `src/sm4_ctr.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr:
	sub sp, sp, #3264
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #3168]
	str x20, [x5, #3176]
	str x21, [x5, #3184]
	str x22, [x5, #3192]
	str x23, [x5, #3200]
	str x24, [x5, #3208]
	str x25, [x5, #3216]
	str x26, [x5, #3224]
	str x27, [x5, #3232]
	str x28, [x5, #3240]
	ldr x6, [x1, #0]
	rev x6, x6
	ldr x7, [x1, #8]
	rev x7, x7
	str x6, [x5, #3248]
	str x7, [x5, #3256]
	movz x10, #0, lsl #0
	adds x7, x7, x3
	adc x6, x6, x10
	rev x6, x6
	rev x7, x7
	str x7, [x1, #8]
	str x6, [x1, #0]
	add x23, x2, #0
	add x24, x3, #0
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	movz x1, #0, lsl #0
	add x2, x5, #0
	movz x3, #396, lsl #0
	bl {vg_sm4_prepare_keys}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	cbz x24, 20f
22:
	ldr x6, [x5, #3248]
	ldr x7, [x5, #3256]
	movz x9, #1, lsl #0
	movz x10, #0, lsl #0
	rev x8, x6
	str x8, [x5, #768]
	rev x8, x7
	str x8, [x5, #776]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #784]
	rev x8, x7
	str x8, [x5, #792]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #800]
	rev x8, x7
	str x8, [x5, #808]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #816]
	rev x8, x7
	str x8, [x5, #824]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #832]
	rev x8, x7
	str x8, [x5, #840]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #848]
	rev x8, x7
	str x8, [x5, #856]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #864]
	rev x8, x7
	str x8, [x5, #872]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #880]
	rev x8, x7
	str x8, [x5, #888]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #896]
	rev x8, x7
	str x8, [x5, #904]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #912]
	rev x8, x7
	str x8, [x5, #920]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #928]
	rev x8, x7
	str x8, [x5, #936]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #944]
	rev x8, x7
	str x8, [x5, #952]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #960]
	rev x8, x7
	str x8, [x5, #968]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #976]
	rev x8, x7
	str x8, [x5, #984]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #992]
	rev x8, x7
	str x8, [x5, #1000]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #1008]
	rev x8, x7
	str x8, [x5, #1016]
	adds x7, x7, x9
	adc x6, x6, x10
	str x6, [x5, #3248]
	str x7, [x5, #3256]
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	add x0, x5, #0
	movz x1, #396, lsl #0
	bl {vg_sm4_crypt_prepared}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	lsr x13, x24, #4
	cbnz x13, 23f
	add x16, x24, #0
	b 24f
23:
	movz x16, #16, lsl #0
24:
	add x14, x5, #0
	add x14, x14, #768
	add x15, x23, #0
	add x17, x16, #0
25:
	ldr x8, [x14, #0]
	ldr x9, [x15, #0]
	eor x8, x8, x9
	str x8, [x15, #0]
	ldr x8, [x14, #8]
	ldr x9, [x15, #8]
	eor x8, x8, x9
	str x8, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 25b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x19, [x5, #3168]
	ldr x20, [x5, #3176]
	ldr x21, [x5, #3184]
	ldr x22, [x5, #3192]
	ldr x23, [x5, #3200]
	ldr x24, [x5, #3208]
	ldr x25, [x5, #3216]
	ldr x26, [x5, #3224]
	ldr x27, [x5, #3232]
	ldr x28, [x5, #3240]
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
	add sp, sp, #3264
	ret
	.p2align 6
