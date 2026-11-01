// The functions of `src/internal/vg_mldsa_multiply_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_ntt:
	lis %r8, 512
	ori %r8, %r8, 32796
	rldicr %r8, %r8, 16, 47
	ori %r8, %r8, 1537
	lis %r9, 127
	ori %r9, %r9, 57345
	li %r6, 256
20:
	lwz %r7, 0(%r4)
	lwz %r10, 0(%r5)
	mulld %r7, %r7, %r10
	mulhdu %r10, %r7, %r8
	mulld %r10, %r10, %r9
	subf %r7, %r10, %r7
	subf %r7, %r9, %r7
	rldicl %r10, %r7, 1, 63
	mulld %r10, %r10, %r9
	add %r7, %r7, %r10
	stw %r7, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	blr
