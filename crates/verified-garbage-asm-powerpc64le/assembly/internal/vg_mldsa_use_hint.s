// The functions of `src/internal/vg_mldsa_use_hint.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_use_hint:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r5
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	lis %r5, 2
	ori %r5, %r5, 59392
	li %r7, 256
22:
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r4)
	addi %r9, %r9, 127
	rldicl %r9, %r9, 57, 7
	mulld %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicl %r9, %r9, 40, 24
	mulld %r0, %r9, %r5
	subf %r0, %r8, %r0
	rldicl %r0, %r0, 1, 63
	rldicr %r0, %r0, 1, 62
	lwz %r8, 0(%r3)
	addi %r8, %r8, -1
	rldicl %r8, %r8, 1, 63
	add %r9, %r9, %r0
	mulld %r0, %r0, %r8
	subf %r9, %r0, %r9
	add %r9, %r9, %r8
	addi %r9, %r9, -1
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	addi %r9, %r9, -44
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	stw %r9, 0(%r6)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	lis %r5, 7
	ori %r5, %r5, 65024
	li %r7, 256
23:
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r4)
	addi %r9, %r9, 127
	rldicl %r9, %r9, 57, 7
	mulld %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicl %r9, %r9, 42, 22
	mulld %r0, %r9, %r5
	subf %r0, %r8, %r0
	rldicl %r0, %r0, 1, 63
	rldicr %r0, %r0, 1, 62
	lwz %r8, 0(%r3)
	addi %r8, %r8, -1
	rldicl %r8, %r8, 1, 63
	add %r9, %r9, %r0
	mulld %r0, %r0, %r8
	subf %r9, %r0, %r9
	add %r9, %r9, %r8
	addi %r9, %r9, -1
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	addi %r9, %r9, -16
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	stw %r9, 0(%r6)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 23b
21:
	blr
