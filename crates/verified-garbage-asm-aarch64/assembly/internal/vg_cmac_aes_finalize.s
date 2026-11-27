// The functions of `src/internal/vg_cmac_aes_finalize.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_finalize:
	sub x9, x4, #16
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x5, #0]
	str x9, [x5, #8]
	add x6, x5, #0
	add x7, x3, #0
	add x8, x4, #0
	cbz x4, 22f
24:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 24b
	b 23f
22:
23:
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x5, #0]
	ldr x10, [x0, #256]
	eor x9, x9, x10
	str x9, [x5, #0]
	ldr x9, [x5, #8]
	ldr x10, [x0, #264]
	eor x9, x9, x10
	str x9, [x5, #8]
	b 21f
20:
	ldr x9, [x3, #0]
	ldr x10, [x0, #240]
	eor x9, x9, x10
	str x9, [x5, #0]
	ldr x9, [x3, #8]
	ldr x10, [x0, #248]
	eor x9, x9, x10
	str x9, [x5, #8]
21:
	ldr x9, [x5, #0]
	ldr x10, [x2, #0]
	eor x9, x9, x10
	str x9, [x5, #0]
	ldr x9, [x5, #8]
	ldr x10, [x2, #8]
	eor x9, x9, x10
	str x9, [x5, #8]
	movz x9, #0, lsl #0
	str x9, [x2, #0]
	str x9, [x2, #8]
	str x19, [x5, #16]
	str x30, [x5, #24]
	add x19, x5, #0
	add x3, x2, #0
	add x2, x5, #0
	movz x4, #1, lsl #0
	add x5, x5, #128
	bl {vg_aes_ctr32}
	ldr x30, [x19, #24]
	ldr x19, [x19, #16]
	ret
	.p2align 6
