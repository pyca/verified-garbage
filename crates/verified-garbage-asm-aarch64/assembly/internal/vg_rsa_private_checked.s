// The functions of `src/internal/vg_rsa_private_checked.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked:
	str x30, [sp, #-16]!
	sub sp, sp, #3232
	add x15, sp, #0
	str x0, [x15, #80]
	str x2, [x15, #88]
	str x3, [x15, #96]
	str x4, [x15, #104]
	str x5, [x15, #112]
	str x6, [x15, #120]
	ldr x8, [sp, #3264]
	str x8, [x15, #0]
	ldr x8, [sp, #3272]
	str x8, [x15, #8]
	ldr x8, [sp, #3280]
	str x8, [x15, #16]
	ldr x8, [sp, #3288]
	str x8, [x15, #24]
	ldr x8, [sp, #3296]
	str x8, [x15, #32]
	ldr x8, [sp, #3304]
	str x8, [x15, #40]
	ldr x8, [sp, #3312]
	str x8, [x15, #48]
	ldr x8, [sp, #3320]
	str x8, [x15, #56]
	ldr x8, [sp, #3328]
	str x8, [x15, #64]
	ldr x8, [sp, #3336]
	str x8, [x15, #72]
	add x0, sp, #160
	add x1, x3, #0
	add x4, x6, #0
	add x5, x3, #0
	ldr x6, [sp, #3248]
	ldr x7, [sp, #3256]
	bl {vg_rsa_private_crt}
	add x15, sp, #0
	str x0, [x15, #128]
	add x0, sp, #1184
	ldr x1, [sp, #96]
	add x1, x1, #7
	lsr x1, x1, #3
	add x1, x1, x1
	ldr x2, [sp, #88]
	ldr x3, [sp, #96]
	ldr x4, [sp, #3328]
	ldr x5, [sp, #3336]
	bl {vg_rsa_public_precompute}
	add x15, sp, #0
	str x0, [x15, #136]
	ldr x0, [sp, #80]
	ldr x1, [sp, #96]
	add x2, sp, #1184
	ldr x3, [sp, #96]
	add x3, x3, #7
	lsr x3, x3, #3
	add x3, x3, x3
	ldr x4, [sp, #104]
	ldr x5, [sp, #112]
	add x6, sp, #160
	add x7, x1, #0
	ldr x8, [sp, #3328]
	str x8, [x15, #0]
	ldr x8, [sp, #3336]
	str x8, [x15, #8]
	bl {vg_rsa_public_precomputed_checked}
	ldr x10, [sp, #128]
	and x9, x0, x10
	ldr x10, [sp, #136]
	and x9, x9, x10
	movz x10, #1, lsl #0
	and x9, x9, x10
	ldr x11, [sp, #80]
	ldr x12, [sp, #120]
	ldr x13, [sp, #96]
	movz x14, #0, lsl #0
20:
	ldrb w8, [x11, #0]
	ldrb w10, [x12, #0]
	eor x8, x8, x10
	orr x14, x14, x8
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 20b
	movz x10, #0, lsl #0
	movz x13, #1, lsl #0
	adds x8, x14, x10
	csel x8, x13, x10, eq
	movz x13, #2, lsl #0
	sub x13, x13, x8
	sub x12, x10, x9
	and x13, x13, x12
	and x8, x8, x9
	sub x12, x10, x8
	ldr x11, [sp, #80]
	add x14, sp, #160
	ldr x15, [sp, #96]
21:
	ldrb w8, [x14, #0]
	and x8, x8, x12
	strb w8, [x11, #0]
	strb w10, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x15, x15, #1
	cbnz x15, 21b
	add x0, x13, #0
	add sp, sp, #3232
	ldr x30, [sp], #16
	ret
	.p2align 6
