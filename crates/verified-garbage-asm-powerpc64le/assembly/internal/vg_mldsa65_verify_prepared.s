// The functions of `src/internal/vg_mldsa65_verify_prepared.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_verify_prepared:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r7, %r3, 1952
	li %r8, 6144
	bl {vg_mldsa65_verify_with_cache}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
