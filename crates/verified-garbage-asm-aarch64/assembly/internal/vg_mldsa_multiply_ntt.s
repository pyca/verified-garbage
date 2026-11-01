// The functions of `src/internal/vg_mldsa_multiply_ntt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_ntt:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz x10, #8191, lsl #0
	movk x10, #65408, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	movz x11, #384, lsl #0
	movk x11, #8199, lsl #16
	movk x11, #128, lsl #32
	movk x11, #0, lsl #48
	movz x12, #256, lsl #0
20:
	ldr w13, [x1, #0]
	ldr w14, [x2, #0]
	mul x13, x13, x14
	lsr x14, x13, #22
	mul x14, x14, x11
	lsr x14, x14, #40
	madd x13, x14, x10, x13
	sub x13, x13, x9
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x0, #0]
	add x0, x0, #4
	add x1, x1, #4
	add x2, x2, #4
	sub x12, x12, #1
	cbnz x12, 20b
	ret
	.p2align 6
