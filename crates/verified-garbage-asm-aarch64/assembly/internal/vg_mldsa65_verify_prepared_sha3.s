// The functions of `src/internal/vg_mldsa65_verify_prepared_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_verify_prepared_sha3:
	str x30, [sp, #-16]!
	add x4, x0, #1952
	movz x5, #6144, lsl #0
	bl {vg_mldsa65_verify_with_cache_sha3}
	ldr x30, [sp], #16
	ret
	.p2align 6
