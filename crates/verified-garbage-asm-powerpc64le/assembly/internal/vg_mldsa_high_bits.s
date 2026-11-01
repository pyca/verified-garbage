// The functions of `src/internal/vg_mldsa_high_bits.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_high_bits:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r4
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	li %r6, 256
22:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 40, 24
	addi %r8, %r8, -44
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	li %r6, 256
23:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 42, 22
	addi %r8, %r8, -16
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
21:
	blr
