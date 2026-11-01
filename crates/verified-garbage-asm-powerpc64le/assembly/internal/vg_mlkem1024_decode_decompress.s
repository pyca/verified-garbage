// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	rlwinm %r5, %r5, 0, 0, 31
	li %r9, 3329
	addi %r7, %r5, -5
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	li %r11, 32
22:
	lbz %r8, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 8, 55
	add %r8, %r8, %r7
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 16, 47
	add %r8, %r8, %r7
	lbz %r7, 3(%r3)
	rldicr %r7, %r7, 24, 39
	add %r8, %r8, %r7
	lbz %r7, 4(%r3)
	rldicr %r7, %r7, 32, 31
	add %r8, %r8, %r7
	lbz %r7, 5(%r3)
	rldicr %r7, %r7, 40, 23
	add %r8, %r8, %r7
	lbz %r12, 5(%r3)
	lbz %r7, 6(%r3)
	rldicr %r7, %r7, 8, 55
	add %r12, %r12, %r7
	lbz %r7, 7(%r3)
	rldicr %r7, %r7, 16, 47
	add %r12, %r12, %r7
	lbz %r7, 8(%r3)
	rldicr %r7, %r7, 24, 39
	add %r12, %r12, %r7
	lbz %r7, 9(%r3)
	rldicr %r7, %r7, 32, 31
	add %r12, %r12, %r7
	lbz %r7, 10(%r3)
	rldicr %r7, %r7, 40, 23
	add %r12, %r12, %r7
	rldicr %r7, %r8, 53, 10
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 42, 21
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 31, 32
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 20, 43
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 12(%r6)
	rldicr %r7, %r12, 49, 14
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 16(%r6)
	rldicr %r7, %r12, 38, 25
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 20(%r6)
	rldicr %r7, %r12, 27, 36
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 24(%r6)
	rldicr %r7, %r12, 16, 47
	rldicl %r7, %r7, 11, 53
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1024
	rldicl %r7, %r7, 53, 11
	stw %r7, 28(%r6)
	addi %r3, %r3, 11
	addi %r6, %r6, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	b 21f
20:
	li %r11, 32
23:
	lbz %r8, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 8, 55
	add %r8, %r8, %r7
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 16, 47
	add %r8, %r8, %r7
	lbz %r7, 3(%r3)
	rldicr %r7, %r7, 24, 39
	add %r8, %r8, %r7
	lbz %r7, 4(%r3)
	rldicr %r7, %r7, 32, 31
	add %r8, %r8, %r7
	rldicr %r7, %r8, 59, 4
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 54, 9
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 49, 14
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 44, 19
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 12(%r6)
	rldicr %r7, %r8, 39, 24
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 16(%r6)
	rldicr %r7, %r8, 34, 29
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 20(%r6)
	rldicr %r7, %r8, 29, 34
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 24(%r6)
	rldicr %r7, %r8, 24, 39
	rldicl %r7, %r7, 5, 59
	mulld %r7, %r7, %r9
	addi %r7, %r7, 16
	rldicl %r7, %r7, 59, 5
	stw %r7, 28(%r6)
	addi %r3, %r3, 5
	addi %r6, %r6, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
21:
	blr
