// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	str x19, [x3, #256]
	str x20, [x3, #264]
	str x30, [x3, #272]
	add x19, x1, #0
	add x20, x2, #0
	add x1, x3, #0
	cbz x20, 20f
22:
	bl {vg_chacha20_block}
	lsr x9, x20, #6
	add x2, x20, #0
	cbz x9, 23f
	movz x2, #64, lsl #0
	b 24f
23:
24:
	sub x20, x20, x2
	add x7, x1, #0
25:
	ldrb w6, [x19, #0]
	ldrb w8, [x7, #0]
	eor w6, w6, w8
	strb w6, [x19, #0]
	add x19, x19, #1
	add x7, x7, #1
	sub x2, x2, #1
	cbnz x2, 25b
	ldr w3, [x0, #48]
	add w3, w3, #1
	str w3, [x0, #48]
	cbnz x20, 22b
	b 21f
20:
21:
	ldr x19, [x1, #256]
	ldr x20, [x1, #264]
	ldr x30, [x1, #272]
	ret
	.p2align 6
