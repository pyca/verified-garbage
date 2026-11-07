// The functions of `src/dit.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dit_enter:
	mrs x0, DIT
	lsr x0, x0, #24
	cbz x0, 20f
	b 21f
20:
	msr DIT, #1
21:
	ret
	.p2align 6

vg_dit_clear:
	msr DIT, #0
	ret
	.p2align 6
