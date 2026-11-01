// The functions of `src/internal/vg_cmac_aes_subkeys_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys_aes:
	.arch_extension aes
	str x19, [x3, #2064]
	str x20, [x3, #2072]
	str x30, [x3, #2080]
	add x19, x2, #0
	add x20, x3, #0
	movz x9, #0, lsl #0
	str x9, [x3, #2048]
	str x9, [x3, #2056]
	str x9, [x2, #0]
	str x9, [x2, #8]
	add x2, x20, #2048
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #0]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #16]
	str x10, [x19, #24]
	ldr x30, [x20, #2080]
	ldr x19, [x20, #2064]
	ldr x20, [x20, #2072]
	ret
	.arch_extension noaes
	.p2align 6
