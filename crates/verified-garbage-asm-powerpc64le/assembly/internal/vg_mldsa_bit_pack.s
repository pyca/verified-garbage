// The functions of `src/internal/vg_mldsa_bit_pack.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_pack:
	addi %r10, %r3, 0
	addi %r11, %r6, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r9, 2
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 4
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r9, 4096
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	lis %r9, 2
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	lis %r4, 8
	li %r12, 128
28:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 5
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	b 27f
26:
	lis %r4, 2
	li %r12, 64
29:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 5(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 6(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 7(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 8(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 9
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
27:
	b 25f
24:
	li %r4, 4096
	li %r12, 32
210:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 5(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 16(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 6(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 7(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 20(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	stb %r8, 8(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 24(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 9(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 10(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 28(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	stb %r8, 11(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 12(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 32
	addi %r11, %r11, 13
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
25:
	b 23f
22:
	li %r4, 4
	li %r12, 128
211:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
23:
	b 21f
20:
	li %r4, 2
	li %r12, 32
212:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	lwz %r9, 16(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lwz %r9, 20(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 24(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lwz %r9, 28(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 32
	addi %r11, %r11, 3
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
21:
	blr
