// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	rlwinm %r4, %r4, 0, 0, 31
	li %r9, 1
	li %r10, 256
	lis %r5, 127
	ori %r5, %r5, 57345
20:
	lwz %r6, 0(%r3)
	subf %r7, %r4, %r6
	rldicl %r7, %r7, 1, 63
	subf %r8, %r6, %r5
	subf %r8, %r4, %r8
	rldicl %r8, %r8, 1, 63
	or %r7, %r7, %r8
	and %r9, %r9, %r7
	addi %r3, %r3, 4
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 20b
	or %r3, %r9, %r9
	blr
