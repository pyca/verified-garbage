// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	add w1, w1, #0
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz x10, #0, lsl #0
	sub x10, x10, #1
	movz x11, #256, lsl #0
20:
	ldr w12, [x0, #0]
	sub x13, x12, x1
	sub x14, x9, x12
	sub x14, x14, x1
	orr x13, x13, x14
	and x10, x10, x13
	add x0, x0, #4
	sub x11, x11, #1
	cbnz x11, 20b
	lsr x0, x10, #63
	ret
	.p2align 6
