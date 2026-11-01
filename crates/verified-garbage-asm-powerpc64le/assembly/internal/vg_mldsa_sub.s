// The functions of `src/internal/vg_mldsa_sub.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sub:
	li %r5, 256
	lis %r8, 127
	ori %r8, %r8, 57345
20:
	lwz %r6, 0(%r3)
	lwz %r7, 0(%r4)
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr
