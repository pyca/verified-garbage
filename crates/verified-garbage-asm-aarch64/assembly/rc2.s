// The functions of `src/rc2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	sub sp, sp, #576
	add x6, sp, #0
	sub x8, x1, #1
	lsr x8, x8, #7
	cbnz x8, 20f
	sub x8, x2, #1
	lsr x8, x8, #10
	cbnz x8, 22f
	sub x8, x4, #8
	cbnz x8, 24f
	str x30, [sp, #-16]!
	ldr x8, [x3, #0]
	str x8, [x5, #128]
	add x3, x5, #0
	add x4, x6, #0
	bl {vg_rc2_expand_key}
	movz x0, #0, lsl #0
	ldr x30, [sp], #16
	b 25f
24:
	movz x0, #3, lsl #0
25:
	b 23f
22:
	movz x0, #2, lsl #0
23:
	b 21f
20:
	movz x0, #1, lsl #0
21:
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
	add sp, sp, #576
	ret
	.p2align 6

vg_rc2_cbc_encrypt_update:
	sub sp, sp, #576
	add x6, sp, #0
	cbz x5, 20f
	str x30, [sp, #-16]!
	add x10, x0, #0
	add x11, x4, #0
	add x12, x1, #0
	cbz x12, 22f
24:
	ldrb w9, [x10, #136]
	strb w9, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 24b
	b 23f
22:
23:
	sub x12, x5, x1
	cbz x12, 25f
27:
	ldrb w9, [x2, #0]
	strb w9, [x11, #0]
	add x2, x2, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	b 26f
25:
26:
	add x3, x3, x1
	sub x3, x3, x5
	add x10, x0, #0
	cbz x3, 28f
210:
	ldrb w9, [x2, #0]
	strb w9, [x10, #136]
	add x2, x2, #1
	add x10, x10, #1
	sub x3, x3, #1
	cbnz x3, 210b
	b 29f
28:
29:
	add x1, x0, #128
	add x2, x4, #0
	lsr x3, x5, #3
	add x4, x6, #0
	bl {vg_rc2_cbc_encrypt}
	ldr x30, [sp], #16
	b 21f
20:
	add x8, x0, x1
	cbz x3, 211f
213:
	ldrb w9, [x2, #0]
	strb w9, [x8, #136]
	add x2, x2, #1
	add x8, x8, #1
	sub x3, x3, #1
	cbnz x3, 213b
	b 212f
211:
212:
21:
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
	add sp, sp, #576
	ret
	.p2align 6

vg_rc2_cbc_decrypt_update:
	sub sp, sp, #576
	add x6, sp, #0
	cbz x5, 20f
	str x30, [sp, #-16]!
	add x10, x0, #0
	add x11, x4, #0
	add x12, x1, #0
	cbz x12, 22f
24:
	ldrb w9, [x10, #136]
	strb w9, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 24b
	b 23f
22:
23:
	sub x12, x5, x1
	cbz x12, 25f
27:
	ldrb w9, [x2, #0]
	strb w9, [x11, #0]
	add x2, x2, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	b 26f
25:
26:
	add x3, x3, x1
	sub x3, x3, x5
	add x10, x0, #0
	cbz x3, 28f
210:
	ldrb w9, [x2, #0]
	strb w9, [x10, #136]
	add x2, x2, #1
	add x10, x10, #1
	sub x3, x3, #1
	cbnz x3, 210b
	b 29f
28:
29:
	add x1, x0, #128
	add x2, x4, #0
	lsr x3, x5, #3
	add x4, x6, #0
	bl {vg_rc2_cbc_decrypt}
	ldr x30, [sp], #16
	b 21f
20:
	add x8, x0, x1
	cbz x3, 211f
213:
	ldrb w9, [x2, #0]
	strb w9, [x8, #136]
	add x2, x2, #1
	add x8, x8, #1
	sub x3, x3, #1
	cbnz x3, 213b
	b 212f
211:
212:
21:
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
	add sp, sp, #576
	ret
	.p2align 6
