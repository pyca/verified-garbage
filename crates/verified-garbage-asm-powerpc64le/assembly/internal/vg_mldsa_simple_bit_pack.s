// The functions of `src/internal/vg_mldsa_simple_bit_pack.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_simple_bit_pack:
	addi %r10, %r3, 0
	addi %r11, %r5, 0
	li %r9, 15
	subf %r9, %r9, %r4
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 43
	subf %r9, %r9, %r4
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r12, 64
24:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 5
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
	li %r12, 64
25:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 3
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
23:
	b 21f
20:
	li %r12, 128
26:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
21:
	blr
