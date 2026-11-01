// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	rlwinm %r4, %r4, 0, 0, 31
	addi %r7, %r4, -5
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	lis %r10, 3
	ori %r10, %r10, 65280
	lis %r9, 4
	ori %r9, %r9, 60398
	li %r11, 32
22:
	li %r8, 0
	li %r12, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 11, 53
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 22, 42
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 33, 31
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 44, 20
	add %r8, %r8, %r7
	lwz %r7, 16(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 15, 49
	add %r12, %r12, %r7
	lwz %r7, 20(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 26, 38
	add %r12, %r12, %r7
	lwz %r7, 24(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 37, 27
	add %r12, %r12, %r7
	lwz %r7, 28(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 53, 10
	rldicl %r7, %r7, 48, 16
	add %r12, %r12, %r7
	stb %r8, 0(%r5)
	rldicl %r7, %r8, 56, 8
	stb %r7, 1(%r5)
	rldicl %r7, %r8, 48, 16
	stb %r7, 2(%r5)
	rldicl %r7, %r8, 40, 24
	stb %r7, 3(%r5)
	rldicl %r7, %r8, 32, 32
	stb %r7, 4(%r5)
	rldicl %r8, %r8, 24, 40
	add %r8, %r8, %r12
	stb %r8, 5(%r5)
	rldicl %r7, %r8, 56, 8
	stb %r7, 6(%r5)
	rldicl %r7, %r8, 48, 16
	stb %r7, 7(%r5)
	rldicl %r7, %r8, 40, 24
	stb %r7, 8(%r5)
	rldicl %r7, %r8, 32, 32
	stb %r7, 9(%r5)
	rldicl %r7, %r8, 24, 40
	stb %r7, 10(%r5)
	addi %r3, %r3, 32
	addi %r5, %r5, 11
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 3
	ori %r10, %r10, 65280
	li %r9, 5040
	li %r11, 32
23:
	li %r8, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 5, 59
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 10, 54
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 15, 49
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 20, 44
	add %r8, %r8, %r7
	lwz %r7, 16(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 25, 39
	add %r8, %r8, %r7
	lwz %r7, 20(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 30, 34
	add %r8, %r8, %r7
	lwz %r7, 24(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 35, 29
	add %r8, %r8, %r7
	lwz %r7, 28(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 59, 4
	rldicl %r7, %r7, 40, 24
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	rldicl %r7, %r8, 56, 8
	stb %r7, 1(%r5)
	rldicl %r7, %r8, 48, 16
	stb %r7, 2(%r5)
	rldicl %r7, %r8, 40, 24
	stb %r7, 3(%r5)
	rldicl %r7, %r8, 32, 32
	stb %r7, 4(%r5)
	addi %r3, %r3, 32
	addi %r5, %r5, 5
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
21:
	blr
