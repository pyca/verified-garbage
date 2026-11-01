// The functions of `src/internal/vg_mldsa_bit_unpack.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_unpack:
	addi %r10, %r3, 0
	addi %r11, %r7, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r9, 2
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 4
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r9, 4096
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	lis %r9, 2
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	lis %r4, 8
	li %r12, 128
28:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	b 27f
26:
	lis %r4, 2
	li %r12, 64
29:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 14, 49
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	addi %r10, %r10, 9
	addi %r11, %r11, 16
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
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 11, 52
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 9, 54
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 16(%r11)
	lbz %r9, 9(%r10)
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 20(%r11)
	lbz %r9, 10(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 11(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 24(%r11)
	lbz %r9, 12(%r10)
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 28(%r11)
	addi %r10, %r10, 13
	addi %r11, %r11, 32
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
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	rldicl %r8, %r8, 60, 4
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	rldicl %r8, %r8, 60, 4
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 8
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
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 16(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 20(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 24(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 28(%r11)
	addi %r10, %r10, 3
	addi %r11, %r11, 32
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
21:
	blr
