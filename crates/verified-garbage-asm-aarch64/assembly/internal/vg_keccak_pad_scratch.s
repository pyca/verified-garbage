// The functions of `src/internal/vg_keccak_pad_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad_scratch:
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	ret
	.p2align 6
