// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	li %r6, 256
	lis %r7, 127
	ori %r7, %r7, 57345
20:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 4095
	rldicl %r9, %r8, 51, 13
	stw %r9, 0(%r4)
	rldicr %r10, %r9, 13, 50
	subf %r8, %r10, %r8
	addi %r8, %r8, -4095
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r7
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	blr
