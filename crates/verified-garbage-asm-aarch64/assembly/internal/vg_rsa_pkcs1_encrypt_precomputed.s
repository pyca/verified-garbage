// The functions of `src/internal/vg_rsa_pkcs1_encrypt_precomputed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
