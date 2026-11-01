// The functions of `src/internal/vg_rc2_cbc_encrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt:
	str x23, [x4, #264]
	str x24, [x4, #272]
	str x30, [x4, #280]
	add x23, x1, #0
	add x24, x3, #0
	add x1, x2, #0
	add x2, x4, #0
	cbz x24, 20f
22:
	ldr x8, [x1, #0]
	ldr x9, [x23, #0]
	eor x8, x8, x9
	str x8, [x1, #0]
	bl {vg_rc2_encrypt_block}
	ldr x8, [x1, #0]
	str x8, [x23, #0]
	add x1, x1, #8
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x23, [x2, #264]
	ldr x24, [x2, #272]
	ldr x30, [x2, #280]
	ret
	.p2align 6
