// The functions of `src/internal/vg_mldsa87_sign_prepared.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_sign_prepared:
	str x30, [sp, #-16]!
	movz x5, #4896, lsl #0
	add x5, x0, x5
	movz x6, #23552, lsl #0
	bl {vg_mldsa87_sign_with_cache}
	ldr x30, [sp], #16
	ret
	.p2align 6
