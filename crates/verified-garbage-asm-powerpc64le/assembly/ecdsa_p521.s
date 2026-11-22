// The functions of `src/ecdsa_p521.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_verify:
	stdu %r1, -112(%r1)
	addi %r8, %r1, 32
	li %r11, 66
	subf %r12, %r11, %r5
	xor %r11, %r5, %r12
	and %r12, %r11, %r12
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	lbz %r9, 0(%r4)
	stb %r9, 0(%r8)
	lbz %r9, 1(%r4)
	stb %r9, 1(%r8)
	lbz %r9, 2(%r4)
	stb %r9, 2(%r8)
	lbz %r9, 3(%r4)
	stb %r9, 3(%r8)
	lbz %r9, 4(%r4)
	stb %r9, 4(%r8)
	lbz %r9, 5(%r4)
	stb %r9, 5(%r8)
	lbz %r9, 6(%r4)
	stb %r9, 6(%r8)
	lbz %r9, 7(%r4)
	stb %r9, 7(%r8)
	lbz %r9, 8(%r4)
	stb %r9, 8(%r8)
	lbz %r9, 9(%r4)
	stb %r9, 9(%r8)
	lbz %r9, 10(%r4)
	stb %r9, 10(%r8)
	lbz %r9, 11(%r4)
	stb %r9, 11(%r8)
	lbz %r9, 12(%r4)
	stb %r9, 12(%r8)
	lbz %r9, 13(%r4)
	stb %r9, 13(%r8)
	lbz %r9, 14(%r4)
	stb %r9, 14(%r8)
	lbz %r9, 15(%r4)
	stb %r9, 15(%r8)
	lbz %r9, 16(%r4)
	stb %r9, 16(%r8)
	lbz %r9, 17(%r4)
	stb %r9, 17(%r8)
	lbz %r9, 18(%r4)
	stb %r9, 18(%r8)
	lbz %r9, 19(%r4)
	stb %r9, 19(%r8)
	lbz %r9, 20(%r4)
	stb %r9, 20(%r8)
	lbz %r9, 21(%r4)
	stb %r9, 21(%r8)
	lbz %r9, 22(%r4)
	stb %r9, 22(%r8)
	lbz %r9, 23(%r4)
	stb %r9, 23(%r8)
	lbz %r9, 24(%r4)
	stb %r9, 24(%r8)
	lbz %r9, 25(%r4)
	stb %r9, 25(%r8)
	lbz %r9, 26(%r4)
	stb %r9, 26(%r8)
	lbz %r9, 27(%r4)
	stb %r9, 27(%r8)
	lbz %r9, 28(%r4)
	stb %r9, 28(%r8)
	lbz %r9, 29(%r4)
	stb %r9, 29(%r8)
	lbz %r9, 30(%r4)
	stb %r9, 30(%r8)
	lbz %r9, 31(%r4)
	stb %r9, 31(%r8)
	lbz %r9, 32(%r4)
	stb %r9, 32(%r8)
	lbz %r9, 33(%r4)
	stb %r9, 33(%r8)
	lbz %r9, 34(%r4)
	stb %r9, 34(%r8)
	lbz %r9, 35(%r4)
	stb %r9, 35(%r8)
	lbz %r9, 36(%r4)
	stb %r9, 36(%r8)
	lbz %r9, 37(%r4)
	stb %r9, 37(%r8)
	lbz %r9, 38(%r4)
	stb %r9, 38(%r8)
	lbz %r9, 39(%r4)
	stb %r9, 39(%r8)
	lbz %r9, 40(%r4)
	stb %r9, 40(%r8)
	lbz %r9, 41(%r4)
	stb %r9, 41(%r8)
	lbz %r9, 42(%r4)
	stb %r9, 42(%r8)
	lbz %r9, 43(%r4)
	stb %r9, 43(%r8)
	lbz %r9, 44(%r4)
	stb %r9, 44(%r8)
	lbz %r9, 45(%r4)
	stb %r9, 45(%r8)
	lbz %r9, 46(%r4)
	stb %r9, 46(%r8)
	lbz %r9, 47(%r4)
	stb %r9, 47(%r8)
	lbz %r9, 48(%r4)
	stb %r9, 48(%r8)
	lbz %r9, 49(%r4)
	stb %r9, 49(%r8)
	lbz %r9, 50(%r4)
	stb %r9, 50(%r8)
	lbz %r9, 51(%r4)
	stb %r9, 51(%r8)
	lbz %r9, 52(%r4)
	stb %r9, 52(%r8)
	lbz %r9, 53(%r4)
	stb %r9, 53(%r8)
	lbz %r9, 54(%r4)
	stb %r9, 54(%r8)
	lbz %r9, 55(%r4)
	stb %r9, 55(%r8)
	lbz %r9, 56(%r4)
	stb %r9, 56(%r8)
	lbz %r9, 57(%r4)
	stb %r9, 57(%r8)
	lbz %r9, 58(%r4)
	stb %r9, 58(%r8)
	lbz %r9, 59(%r4)
	stb %r9, 59(%r8)
	lbz %r9, 60(%r4)
	stb %r9, 60(%r8)
	lbz %r9, 61(%r4)
	stb %r9, 61(%r8)
	lbz %r9, 62(%r4)
	stb %r9, 62(%r8)
	lbz %r9, 63(%r4)
	stb %r9, 63(%r8)
	lbz %r9, 64(%r4)
	stb %r9, 64(%r8)
	lbz %r9, 65(%r4)
	stb %r9, 65(%r8)
	b 21f
20:
	li %r9, 0
	stb %r9, 0(%r8)
	stb %r9, 1(%r8)
	stb %r9, 2(%r8)
	stb %r9, 3(%r8)
	stb %r9, 4(%r8)
	stb %r9, 5(%r8)
	stb %r9, 6(%r8)
	stb %r9, 7(%r8)
	stb %r9, 8(%r8)
	stb %r9, 9(%r8)
	stb %r9, 10(%r8)
	stb %r9, 11(%r8)
	stb %r9, 12(%r8)
	stb %r9, 13(%r8)
	stb %r9, 14(%r8)
	stb %r9, 15(%r8)
	stb %r9, 16(%r8)
	stb %r9, 17(%r8)
	stb %r9, 18(%r8)
	stb %r9, 19(%r8)
	stb %r9, 20(%r8)
	stb %r9, 21(%r8)
	stb %r9, 22(%r8)
	stb %r9, 23(%r8)
	stb %r9, 24(%r8)
	stb %r9, 25(%r8)
	stb %r9, 26(%r8)
	stb %r9, 27(%r8)
	stb %r9, 28(%r8)
	stb %r9, 29(%r8)
	stb %r9, 30(%r8)
	stb %r9, 31(%r8)
	stb %r9, 32(%r8)
	stb %r9, 33(%r8)
	stb %r9, 34(%r8)
	stb %r9, 35(%r8)
	stb %r9, 36(%r8)
	stb %r9, 37(%r8)
	stb %r9, 38(%r8)
	stb %r9, 39(%r8)
	stb %r9, 40(%r8)
	stb %r9, 41(%r8)
	stb %r9, 42(%r8)
	stb %r9, 43(%r8)
	stb %r9, 44(%r8)
	stb %r9, 45(%r8)
	stb %r9, 46(%r8)
	stb %r9, 47(%r8)
	stb %r9, 48(%r8)
	stb %r9, 49(%r8)
	stb %r9, 50(%r8)
	stb %r9, 51(%r8)
	stb %r9, 52(%r8)
	stb %r9, 53(%r8)
	stb %r9, 54(%r8)
	stb %r9, 55(%r8)
	stb %r9, 56(%r8)
	stb %r9, 57(%r8)
	stb %r9, 58(%r8)
	stb %r9, 59(%r8)
	stb %r9, 60(%r8)
	stb %r9, 61(%r8)
	stb %r9, 62(%r8)
	stb %r9, 63(%r8)
	stb %r9, 64(%r8)
	stb %r9, 65(%r8)
	stb %r9, 66(%r8)
	stb %r9, 67(%r8)
	stb %r9, 68(%r8)
	stb %r9, 69(%r8)
	stb %r9, 70(%r8)
	stb %r9, 71(%r8)
	addi %r10, %r8, 66
	subf %r10, %r5, %r10
	cmpldi %cr0, %r5, 0
	beq %cr0, 22f
24:
	lbz %r9, 0(%r4)
	stb %r9, 0(%r10)
	addi %r4, %r4, 1
	addi %r10, %r10, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	b 23f
22:
23:
	lbz %r9, 0(%r8)
	lbz %r10, 1(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 0(%r8)
	lbz %r9, 1(%r8)
	lbz %r10, 2(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 1(%r8)
	lbz %r9, 2(%r8)
	lbz %r10, 3(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 2(%r8)
	lbz %r9, 3(%r8)
	lbz %r10, 4(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 3(%r8)
	lbz %r9, 4(%r8)
	lbz %r10, 5(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 4(%r8)
	lbz %r9, 5(%r8)
	lbz %r10, 6(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 5(%r8)
	lbz %r9, 6(%r8)
	lbz %r10, 7(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 6(%r8)
	lbz %r9, 7(%r8)
	lbz %r10, 8(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 7(%r8)
	lbz %r9, 8(%r8)
	lbz %r10, 9(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 8(%r8)
	lbz %r9, 9(%r8)
	lbz %r10, 10(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 9(%r8)
	lbz %r9, 10(%r8)
	lbz %r10, 11(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 10(%r8)
	lbz %r9, 11(%r8)
	lbz %r10, 12(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 11(%r8)
	lbz %r9, 12(%r8)
	lbz %r10, 13(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 12(%r8)
	lbz %r9, 13(%r8)
	lbz %r10, 14(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 13(%r8)
	lbz %r9, 14(%r8)
	lbz %r10, 15(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 14(%r8)
	lbz %r9, 15(%r8)
	lbz %r10, 16(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 15(%r8)
	lbz %r9, 16(%r8)
	lbz %r10, 17(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 16(%r8)
	lbz %r9, 17(%r8)
	lbz %r10, 18(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 17(%r8)
	lbz %r9, 18(%r8)
	lbz %r10, 19(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 18(%r8)
	lbz %r9, 19(%r8)
	lbz %r10, 20(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 19(%r8)
	lbz %r9, 20(%r8)
	lbz %r10, 21(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 20(%r8)
	lbz %r9, 21(%r8)
	lbz %r10, 22(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 21(%r8)
	lbz %r9, 22(%r8)
	lbz %r10, 23(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 22(%r8)
	lbz %r9, 23(%r8)
	lbz %r10, 24(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 23(%r8)
	lbz %r9, 24(%r8)
	lbz %r10, 25(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 24(%r8)
	lbz %r9, 25(%r8)
	lbz %r10, 26(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 25(%r8)
	lbz %r9, 26(%r8)
	lbz %r10, 27(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 26(%r8)
	lbz %r9, 27(%r8)
	lbz %r10, 28(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 27(%r8)
	lbz %r9, 28(%r8)
	lbz %r10, 29(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 28(%r8)
	lbz %r9, 29(%r8)
	lbz %r10, 30(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 29(%r8)
	lbz %r9, 30(%r8)
	lbz %r10, 31(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 30(%r8)
	lbz %r9, 31(%r8)
	lbz %r10, 32(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 31(%r8)
	lbz %r9, 32(%r8)
	lbz %r10, 33(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 32(%r8)
	lbz %r9, 33(%r8)
	lbz %r10, 34(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 33(%r8)
	lbz %r9, 34(%r8)
	lbz %r10, 35(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 34(%r8)
	lbz %r9, 35(%r8)
	lbz %r10, 36(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 35(%r8)
	lbz %r9, 36(%r8)
	lbz %r10, 37(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 36(%r8)
	lbz %r9, 37(%r8)
	lbz %r10, 38(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 37(%r8)
	lbz %r9, 38(%r8)
	lbz %r10, 39(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 38(%r8)
	lbz %r9, 39(%r8)
	lbz %r10, 40(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 39(%r8)
	lbz %r9, 40(%r8)
	lbz %r10, 41(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 40(%r8)
	lbz %r9, 41(%r8)
	lbz %r10, 42(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 41(%r8)
	lbz %r9, 42(%r8)
	lbz %r10, 43(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 42(%r8)
	lbz %r9, 43(%r8)
	lbz %r10, 44(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 43(%r8)
	lbz %r9, 44(%r8)
	lbz %r10, 45(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 44(%r8)
	lbz %r9, 45(%r8)
	lbz %r10, 46(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 45(%r8)
	lbz %r9, 46(%r8)
	lbz %r10, 47(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 46(%r8)
	lbz %r9, 47(%r8)
	lbz %r10, 48(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 47(%r8)
	lbz %r9, 48(%r8)
	lbz %r10, 49(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 48(%r8)
	lbz %r9, 49(%r8)
	lbz %r10, 50(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 49(%r8)
	lbz %r9, 50(%r8)
	lbz %r10, 51(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 50(%r8)
	lbz %r9, 51(%r8)
	lbz %r10, 52(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 51(%r8)
	lbz %r9, 52(%r8)
	lbz %r10, 53(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 52(%r8)
	lbz %r9, 53(%r8)
	lbz %r10, 54(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 53(%r8)
	lbz %r9, 54(%r8)
	lbz %r10, 55(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 54(%r8)
	lbz %r9, 55(%r8)
	lbz %r10, 56(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 55(%r8)
	lbz %r9, 56(%r8)
	lbz %r10, 57(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 56(%r8)
	lbz %r9, 57(%r8)
	lbz %r10, 58(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 57(%r8)
	lbz %r9, 58(%r8)
	lbz %r10, 59(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 58(%r8)
	lbz %r9, 59(%r8)
	lbz %r10, 60(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 59(%r8)
	lbz %r9, 60(%r8)
	lbz %r10, 61(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 60(%r8)
	lbz %r9, 61(%r8)
	lbz %r10, 62(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 61(%r8)
	lbz %r9, 62(%r8)
	lbz %r10, 63(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 62(%r8)
	lbz %r9, 63(%r8)
	lbz %r10, 64(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 63(%r8)
	lbz %r9, 64(%r8)
	lbz %r10, 65(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 64(%r8)
	lbz %r9, 65(%r8)
	lbz %r10, 66(%r8)
	rldicr %r9, %r9, 7, 56
	rldicl %r10, %r10, 63, 1
	add %r9, %r9, %r10
	stb %r9, 65(%r8)
21:
	or %r4, %r8, %r8
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 58
	ldbrx %r8, %r5, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r5, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r5, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r5, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r5, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r5, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r5, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r5, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	ld %r4, 2368(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2376(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2368(%r3)
	ld %r4, 2376(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2384(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2376(%r3)
	ld %r4, 2384(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2392(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2384(%r3)
	ld %r4, 2392(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2400(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2392(%r3)
	ld %r4, 2400(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2408(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2400(%r3)
	ld %r4, 2408(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2416(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2408(%r3)
	ld %r4, 2416(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2424(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2416(%r3)
	ld %r4, 2424(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2432(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2424(%r3)
	ld %r4, 2432(%r3)
	rldicl %r4, %r4, 57, 7
	std %r4, 2432(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P521_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P521_FRAME_CONSTS}
	mtlr %r11
	li %r31, 153
25:
	addi %r31, %r31, -1
	rldicr %r8, %r31, 3, 60
	add %r9, %r4, %r8
	ld %r11, 0(%r9)
	add %r9, %r3, %r8
	std %r11, 64(%r9)
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 3232(%r3)
	or %r12, %r5, %r5
	li %r31, 72
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2296(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r31, 72
27:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 928(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4672(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4673(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4674(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4675(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4676(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4677(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4678(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4679(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r31, 72
28:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1000(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5248(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5249(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5250(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5251(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5252(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5253(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5254(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5255(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	addi %r6, %r12, 66
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2224(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2232(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2240(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2248(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2256(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2264(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2272(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2280(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2288(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2876(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2880(%r3)
	lis %r11, 0
	ori %r11, %r11, 16384
	stw %r11, 2884(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2888(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2924(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2940(%r3)
	lis %r11, -20904
	ori %r11, %r11, 25479
	stw %r11, 2944(%r3)
	lis %r11, -32748
	ori %r11, %r11, 25935
	stw %r11, 2948(%r3)
	lis %r11, -5579
	ori %r11, %r11, 43039
	stw %r11, 2952(%r3)
	lis %r11, 30967
	ori %r11, %r11, 41615
	stw %r11, 2956(%r3)
	lis %r11, -15330
	ori %r11, %r11, 38426
	stw %r11, 2960(%r3)
	lis %r11, -31846
	ori %r11, %r11, 47599
	stw %r11, 2964(%r3)
	lis %r11, 24221
	ori %r11, %r11, 55519
	stw %r11, 2968(%r3)
	lis %r11, -17013
	ori %r11, %r11, 10592
	stw %r11, 2972(%r3)
	lis %r11, -22282
	ori %r11, %r11, 16201
	stw %r11, 2976(%r3)
	lis %r11, -3925
	ori %r11, %r11, 3228
	stw %r11, 2980(%r3)
	lis %r11, -14137
	ori %r11, %r11, 30852
	stw %r11, 2984(%r3)
	lis %r11, -1572
	ori %r11, %r11, 23108
	stw %r11, 2988(%r3)
	lis %r11, 11724
	ori %r11, %r11, 55690
	stw %r11, 2992(%r3)
	lis %r11, 30545
	ori %r11, %r11, 27961
	stw %r11, 2996(%r3)
	lis %r11, -12197
	ori %r11, %r11, 17056
	stw %r11, 3000(%r3)
	lis %r11, 4041
	ori %r11, %r11, 19728
	stw %r11, 3004(%r3)
	lis %r11, 0
	ori %r11, %r11, 77
	stw %r11, 3008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3012(%r3)
	addi %r6, %r14, 1
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	addi %r6, %r6, 66
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2656(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2664(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2672(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2680(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2688(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2696(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2704(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2712(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2720(%r3)
	lbz %r4, 0(%r14)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2440(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2444(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2448(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2452(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2456(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2460(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2464(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2468(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2472(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2476(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2480(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2484(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2488(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2492(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2496(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2500(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2504(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2508(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2656(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2660(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2664(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2668(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2672(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2676(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2680(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2684(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2688(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2692(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2696(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2700(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2704(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2708(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2712(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2716(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2720(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2724(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	bl {vg_p521_validate}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2296(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2300(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2304(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2308(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2312(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2316(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2320(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2324(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2328(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2332(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2336(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2340(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2344(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2348(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2352(%r3)
	lwz %r8, 192(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2356(%r3)
	lwz %r8, 196(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2360(%r3)
	lwz %r8, 200(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2364(%r3)
	lwz %r8, 204(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2296(%r3)
	ld %r4, 2304(%r3)
	or %r5, %r5, %r4
	ld %r4, 2312(%r3)
	or %r5, %r5, %r4
	ld %r4, 2320(%r3)
	or %r5, %r5, %r4
	ld %r4, 2328(%r3)
	or %r5, %r5, %r4
	ld %r4, 2336(%r3)
	or %r5, %r5, %r4
	ld %r4, 2344(%r3)
	or %r5, %r5, %r4
	ld %r4, 2352(%r3)
	or %r5, %r5, %r4
	ld %r4, 2360(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2224(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2228(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2232(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2236(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2240(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2244(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2248(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2252(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2256(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2260(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2264(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2268(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2272(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2276(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2280(%r3)
	lwz %r8, 192(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2284(%r3)
	lwz %r8, 196(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2288(%r3)
	lwz %r8, 200(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2292(%r3)
	lwz %r8, 204(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2224(%r3)
	ld %r4, 2232(%r3)
	or %r5, %r5, %r4
	ld %r4, 2240(%r3)
	or %r5, %r5, %r4
	ld %r4, 2248(%r3)
	or %r5, %r5, %r4
	ld %r4, 2256(%r3)
	or %r5, %r5, %r4
	ld %r4, 2264(%r3)
	or %r5, %r5, %r4
	ld %r4, 2272(%r3)
	or %r5, %r5, %r4
	ld %r4, 2280(%r3)
	or %r5, %r5, %r4
	ld %r4, 2288(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r4, 2728
	li %r5, 2224
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	bl {vg_p521_inv_mod_n}
	li %r4, 2944
	li %r5, 2368
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 2872
	li %r5, 2296
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 3016
	li %r5, 2944
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 3088
	li %r5, 2872
	li %r6, 2152
	bl {vg_p521_mul_mod_n}
	li %r4, 2512
	li %r5, 3016
	li %r6, 352
	bl {vg_p521_mul_mod_n}
	li %r4, 2584
	li %r5, 3088
	li %r6, 352
	bl {vg_p521_mul_mod_n}
	li %r31, 72
29:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2512(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	lis %r11, -20904
	ori %r11, %r11, 25479
	stw %r11, 2944(%r3)
	lis %r11, -32748
	ori %r11, %r11, 25935
	stw %r11, 2948(%r3)
	lis %r11, -5579
	ori %r11, %r11, 43039
	stw %r11, 2952(%r3)
	lis %r11, 30967
	ori %r11, %r11, 41615
	stw %r11, 2956(%r3)
	lis %r11, -15330
	ori %r11, %r11, 38426
	stw %r11, 2960(%r3)
	lis %r11, -31846
	ori %r11, %r11, 47599
	stw %r11, 2964(%r3)
	lis %r11, 24221
	ori %r11, %r11, 55519
	stw %r11, 2968(%r3)
	lis %r11, -17013
	ori %r11, %r11, 10592
	stw %r11, 2972(%r3)
	lis %r11, -22282
	ori %r11, %r11, 16201
	stw %r11, 2976(%r3)
	lis %r11, -3925
	ori %r11, %r11, 3228
	stw %r11, 2980(%r3)
	lis %r11, -14137
	ori %r11, %r11, 30852
	stw %r11, 2984(%r3)
	lis %r11, -1572
	ori %r11, %r11, 23108
	stw %r11, 2988(%r3)
	lis %r11, 11724
	ori %r11, %r11, 55690
	stw %r11, 2992(%r3)
	lis %r11, 30545
	ori %r11, %r11, 27961
	stw %r11, 2996(%r3)
	lis %r11, -12197
	ori %r11, %r11, 17056
	stw %r11, 3000(%r3)
	lis %r11, 4041
	ori %r11, %r11, 19728
	stw %r11, 3004(%r3)
	lis %r11, 0
	ori %r11, %r11, 77
	stw %r11, 3008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3012(%r3)
	lis %r11, -6878
	ori %r11, %r11, 61590
	stw %r11, 1072(%r3)
	lis %r11, -10344
	ori %r11, %r11, 41607
	stw %r11, 1076(%r3)
	lis %r11, 720
	ori %r11, %r11, 18515
	stw %r11, 1080(%r3)
	lis %r11, -9319
	ori %r11, %r11, 60402
	stw %r11, 1084(%r3)
	lis %r11, 17447
	ori %r11, %r11, 24542
	stw %r11, 1088(%r3)
	lis %r11, -24013
	ori %r11, %r11, 47269
	stw %r11, 1092(%r3)
	lis %r11, 4921
	ori %r11, %r11, 15950
	stw %r11, 1096(%r3)
	lis %r11, -11902
	ori %r11, %r11, 23456
	stw %r11, 1100(%r3)
	lis %r11, 28692
	ori %r11, %r11, 20147
	stw %r11, 1104(%r3)
	lis %r11, 32632
	ori %r11, %r11, 26015
	stw %r11, 1108(%r3)
	lis %r11, -22511
	ori %r11, %r11, 49528
	stw %r11, 1112(%r3)
	lis %r11, -9925
	ori %r11, %r11, 16258
	stw %r11, 1116(%r3)
	lis %r11, -28245
	ori %r11, %r11, 28933
	stw %r11, 1120(%r3)
	lis %r11, -32197
	ori %r11, %r11, 9736
	stw %r11, 1124(%r3)
	lis %r11, -28861
	ori %r11, %r11, 33104
	stw %r11, 1128(%r3)
	lis %r11, 12426
	ori %r11, %r11, 21220
	stw %r11, 1132(%r3)
	lis %r11, 0
	ori %r11, %r11, 458
	stw %r11, 1136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1140(%r3)
	lis %r11, 23473
	ori %r11, %r11, 10216
	stw %r11, 1144(%r3)
	lis %r11, 19213
	ori %r11, %r11, 63382
	stw %r11, 1148(%r3)
	lis %r11, 5520
	ori %r11, %r11, 27064
	stw %r11, 1152(%r3)
	lis %r11, -952
	ori %r11, %r11, 7397
	stw %r11, 1156(%r3)
	lis %r11, 474
	ori %r11, %r11, 22642
	stw %r11, 1160(%r3)
	lis %r11, -31569
	ori %r11, %r11, 17683
	stw %r11, 1164(%r3)
	lis %r11, -28710
	ori %r11, %r11, 4372
	stw %r11, 1168(%r3)
	lis %r11, 30605
	ori %r11, %r11, 899
	stw %r11, 1172(%r3)
	lis %r11, -2030
	ori %r11, %r11, 32282
	stw %r11, 1176(%r3)
	lis %r11, 14967
	ori %r11, %r11, 19519
	stw %r11, 1180(%r3)
	lis %r11, 1705
	ori %r11, %r11, 13611
	stw %r11, 1184(%r3)
	lis %r11, -26226
	ori %r11, %r11, 64078
	stw %r11, 1188(%r3)
	lis %r11, -272
	ori %r11, %r11, 18212
	stw %r11, 1192(%r3)
	lis %r11, -15124
	ori %r11, %r11, 34805
	stw %r11, 1196(%r3)
	lis %r11, -5390
	ori %r11, %r11, 36247
	stw %r11, 1200(%r3)
	lis %r11, -8030
	ori %r11, %r11, 25429
	stw %r11, 1204(%r3)
	lis %r11, 0
	ori %r11, %r11, 209
	stw %r11, 1208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1216(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1284(%r3)
	li %r31, 83
210:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -82
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	li %r9, 0
	add %r9, %r9, %r9
	lbz %r5, 4102(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4101(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4100(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4099(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	b 212f
211:
	li %r9, 0
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
212:
	addi %r9, %r9, -64
	rldicl %r4, %r9, 1, 63
	li %r5, 0
	subf %r4, %r4, %r5
	xor %r9, %r9, %r4
	subf %r9, %r4, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_P521_COMB}
	addi %r8, %r8, ({VG_P521_COMB}
	li %r4, 9216
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	li %r7, 1
213:
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	mtvsrd 51, %r10
	vspltw %v19, %v19, 0
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v0, %v0, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v1, %v1, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v2, %v2, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v3, %v3, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v4, %v4, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v5, %v5, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v6, %v6, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v7, %v7, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v8, %v8, %v18, %v19
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	li %r4, 1504
	stxvd2x 32, %r3, %r4
	li %r4, 1520
	stxvd2x 33, %r3, %r4
	li %r4, 1536
	stxvd2x 34, %r3, %r4
	li %r4, 1552
	stxvd2x 35, %r3, %r4
	li %r4, 1568
	stxvd2x 36, %r3, %r4
	li %r4, 1584
	stxvd2x 37, %r3, %r4
	li %r4, 1600
	stxvd2x 38, %r3, %r4
	li %r4, 1616
	stxvd2x 39, %r3, %r4
	li %r4, 1632
	stxvd2x 40, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1648(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1652(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1656(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1660(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1664(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1668(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1672(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1676(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1680(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1684(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1688(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1692(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1696(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1700(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1708(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1712(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1716(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 1576(%r3)
	ld %r5, 1648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1576(%r3)
	ld %r4, 1584(%r3)
	ld %r5, 1656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 1592(%r3)
	ld %r5, 1664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 1600(%r3)
	ld %r5, 1672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 1608(%r3)
	ld %r5, 1680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 1616(%r3)
	ld %r5, 1688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 1624(%r3)
	ld %r5, 1696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1624(%r3)
	ld %r4, 1632(%r3)
	ld %r5, 1704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1632(%r3)
	ld %r4, 1640(%r3)
	ld %r5, 1712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1640(%r3)
	ld %r4, 1648(%r3)
	ld %r5, 280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1648(%r3)
	ld %r4, 1656(%r3)
	ld %r5, 288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1656(%r3)
	ld %r4, 1664(%r3)
	ld %r5, 296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1664(%r3)
	ld %r4, 1672(%r3)
	ld %r5, 304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1672(%r3)
	ld %r4, 1680(%r3)
	ld %r5, 312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1680(%r3)
	ld %r4, 1688(%r3)
	ld %r5, 320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1688(%r3)
	ld %r4, 1696(%r3)
	ld %r5, 328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1696(%r3)
	ld %r4, 1704(%r3)
	ld %r5, 336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1704(%r3)
	ld %r4, 1712(%r3)
	ld %r5, 344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1712(%r3)
	li %r4, 1288
	li %r5, 280
	li %r6, 1576
	bl {vg_p521_sub_mod_p}
	addi %r6, %r31, -82
	cmpldi %cr0, %r6, 0
	beq %cr0, 214f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	addi %r10, %r4, -1
	b 215f
214:
	li %r10, 0
	addi %r10, %r10, -1
215:
	ld %r4, 1576(%r3)
	ld %r5, 1288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1576(%r3)
	ld %r4, 1584(%r3)
	ld %r5, 1296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 1592(%r3)
	ld %r5, 1304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 1600(%r3)
	ld %r5, 1312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 1608(%r3)
	ld %r5, 1320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 1616(%r3)
	ld %r5, 1328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 1624(%r3)
	ld %r5, 1336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1624(%r3)
	ld %r4, 1632(%r3)
	ld %r5, 1344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1632(%r3)
	ld %r4, 1640(%r3)
	ld %r5, 1352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1640(%r3)
	li %r4, 1720
	li %r5, 1072
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1144
	li %r6, 1576
	bl {vg_p521_mul_mod_p}
	li %r4, 1864
	li %r5, 1216
	li %r6, 1648
	bl {vg_p521_mul_mod_p}
	li %r4, 1936
	li %r5, 1072
	li %r6, 1144
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 1504
	li %r6, 1576
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 1720
	li %r6, 1792
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_sub_mod_p}
	li %r4, 2008
	li %r5, 1072
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 1504
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_mul_mod_p}
	li %r4, 2080
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_sub_mod_p}
	li %r4, 2080
	li %r5, 1144
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1576
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 496
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 568
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 568
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_sub_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1792
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 2080
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1936
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1288
	li %r6, 1720
	bl {vg_p521_sub_mod_p}
	li %r4, 1720
	li %r5, 1936
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 2080
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1432
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	ld %r4, 1288(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1088(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1096(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1104(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1112(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1120(%r3)
	ld %r4, 1344(%r3)
	std %r4, 1128(%r3)
	ld %r4, 1352(%r3)
	std %r4, 1136(%r3)
	ld %r4, 1360(%r3)
	std %r4, 1144(%r3)
	ld %r4, 1368(%r3)
	std %r4, 1152(%r3)
	ld %r4, 1376(%r3)
	std %r4, 1160(%r3)
	ld %r4, 1384(%r3)
	std %r4, 1168(%r3)
	ld %r4, 1392(%r3)
	std %r4, 1176(%r3)
	ld %r4, 1400(%r3)
	std %r4, 1184(%r3)
	ld %r4, 1408(%r3)
	std %r4, 1192(%r3)
	ld %r4, 1416(%r3)
	std %r4, 1200(%r3)
	ld %r4, 1424(%r3)
	std %r4, 1208(%r3)
	ld %r4, 1432(%r3)
	std %r4, 1216(%r3)
	ld %r4, 1440(%r3)
	std %r4, 1224(%r3)
	ld %r4, 1448(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1456(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1464(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1472(%r3)
	std %r4, 1256(%r3)
	ld %r4, 1480(%r3)
	std %r4, 1264(%r3)
	ld %r4, 1488(%r3)
	std %r4, 1272(%r3)
	ld %r4, 1496(%r3)
	std %r4, 1280(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	ld %r4, 1072(%r3)
	std %r4, 3016(%r3)
	ld %r4, 1080(%r3)
	std %r4, 3024(%r3)
	ld %r4, 1088(%r3)
	std %r4, 3032(%r3)
	ld %r4, 1096(%r3)
	std %r4, 3040(%r3)
	ld %r4, 1104(%r3)
	std %r4, 3048(%r3)
	ld %r4, 1112(%r3)
	std %r4, 3056(%r3)
	ld %r4, 1120(%r3)
	std %r4, 3064(%r3)
	ld %r4, 1128(%r3)
	std %r4, 3072(%r3)
	ld %r4, 1136(%r3)
	std %r4, 3080(%r3)
	ld %r4, 1144(%r3)
	std %r4, 3088(%r3)
	ld %r4, 1152(%r3)
	std %r4, 3096(%r3)
	ld %r4, 1160(%r3)
	std %r4, 3104(%r3)
	ld %r4, 1168(%r3)
	std %r4, 3112(%r3)
	ld %r4, 1176(%r3)
	std %r4, 3120(%r3)
	ld %r4, 1184(%r3)
	std %r4, 3128(%r3)
	ld %r4, 1192(%r3)
	std %r4, 3136(%r3)
	ld %r4, 1200(%r3)
	std %r4, 3144(%r3)
	ld %r4, 1208(%r3)
	std %r4, 3152(%r3)
	ld %r4, 1216(%r3)
	std %r4, 2728(%r3)
	ld %r4, 1224(%r3)
	std %r4, 2736(%r3)
	ld %r4, 1232(%r3)
	std %r4, 2744(%r3)
	ld %r4, 1240(%r3)
	std %r4, 2752(%r3)
	ld %r4, 1248(%r3)
	std %r4, 2760(%r3)
	ld %r4, 1256(%r3)
	std %r4, 2768(%r3)
	ld %r4, 1264(%r3)
	std %r4, 2776(%r3)
	ld %r4, 1272(%r3)
	std %r4, 2784(%r3)
	ld %r4, 1280(%r3)
	std %r4, 2792(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1072(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1076(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1080(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1084(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1088(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1092(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1096(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1100(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1104(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1108(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1112(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1116(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1120(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1124(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1128(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1132(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1144(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1148(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1152(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1156(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1160(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1164(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1168(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1172(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1176(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1180(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1188(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1192(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1196(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1204(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1284(%r3)
	li %r31, 72
216:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2584(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	bl {vg_p521_windows}
	li %r4, 1720
	li %r5, 3016
	li %r6, 1072
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 3088
	li %r6, 1144
	bl {vg_p521_mul_mod_p}
	li %r4, 1864
	li %r5, 2728
	li %r6, 1216
	bl {vg_p521_mul_mod_p}
	li %r4, 1936
	li %r5, 3016
	li %r6, 3088
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 1072
	li %r6, 1144
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 1720
	li %r6, 1792
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_sub_mod_p}
	li %r4, 2008
	li %r5, 3016
	li %r6, 2728
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 1072
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_mul_mod_p}
	li %r4, 2080
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_sub_mod_p}
	li %r4, 2080
	li %r5, 3088
	li %r6, 2728
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1144
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 496
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 568
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 568
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_sub_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1792
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 2080
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1936
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1288
	li %r6, 1720
	bl {vg_p521_sub_mod_p}
	li %r4, 1720
	li %r5, 1936
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 2080
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1432
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	ld %r4, 1288(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1088(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1096(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1104(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1112(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1120(%r3)
	ld %r4, 1344(%r3)
	std %r4, 1128(%r3)
	ld %r4, 1352(%r3)
	std %r4, 1136(%r3)
	ld %r4, 1360(%r3)
	std %r4, 1144(%r3)
	ld %r4, 1368(%r3)
	std %r4, 1152(%r3)
	ld %r4, 1376(%r3)
	std %r4, 1160(%r3)
	ld %r4, 1384(%r3)
	std %r4, 1168(%r3)
	ld %r4, 1392(%r3)
	std %r4, 1176(%r3)
	ld %r4, 1400(%r3)
	std %r4, 1184(%r3)
	ld %r4, 1408(%r3)
	std %r4, 1192(%r3)
	ld %r4, 1416(%r3)
	std %r4, 1200(%r3)
	ld %r4, 1424(%r3)
	std %r4, 1208(%r3)
	ld %r4, 1432(%r3)
	std %r4, 1216(%r3)
	ld %r4, 1440(%r3)
	std %r4, 1224(%r3)
	ld %r4, 1448(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1456(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1464(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1472(%r3)
	std %r4, 1256(%r3)
	ld %r4, 1480(%r3)
	std %r4, 1264(%r3)
	ld %r4, 1488(%r3)
	std %r4, 1272(%r3)
	ld %r4, 1496(%r3)
	std %r4, 1280(%r3)
	bl {vg_p521_inv_mod_p}
	li %r4, 2512
	li %r5, 1072
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2584
	li %r5, 2512
	li %r6, 352
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 2584
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 2944
	li %r5, 2800
	li %r6, 2872
	bl {vg_p521_sub_mod_n}
	ld %r5, 1216(%r3)
	ld %r4, 1224(%r3)
	or %r5, %r5, %r4
	ld %r4, 1232(%r3)
	or %r5, %r5, %r4
	ld %r4, 1240(%r3)
	or %r5, %r5, %r4
	ld %r4, 1248(%r3)
	or %r5, %r5, %r4
	ld %r4, 1256(%r3)
	or %r5, %r5, %r4
	ld %r4, 1264(%r3)
	or %r5, %r5, %r4
	ld %r4, 1272(%r3)
	or %r5, %r5, %r4
	ld %r4, 1280(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r5, 2944(%r3)
	ld %r4, 2952(%r3)
	or %r5, %r5, %r4
	ld %r4, 2960(%r3)
	or %r5, %r5, %r4
	ld %r4, 2968(%r3)
	or %r5, %r5, %r4
	ld %r4, 2976(%r3)
	or %r5, %r5, %r4
	ld %r4, 2984(%r3)
	or %r5, %r5, %r4
	ld %r4, 2992(%r3)
	or %r5, %r5, %r4
	ld %r4, 3000(%r3)
	or %r5, %r5, %r4
	ld %r4, 3008(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	li %r4, 0
	subf %r5, %r5, %r4
	addi %r5, %r5, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	addi %r1, %r1, 112
	li %r0, 0
	stdu %r1, -112(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	addi %r1, %r1, 112
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_ecdsa_p521_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -592(%r1)
	addi %r11, %r1, 0
	std %r3, 200(%r11)
	std %r4, 192(%r11)
	std %r5, 184(%r11)
	std %r7, 176(%r11)
	std %r8, 224(%r11)
	ld %r9, 32(%r8)
	std %r9, 208(%r11)
	ld %r9, 40(%r8)
	std %r9, 216(%r11)
	addi %r11, %r1, 0
	li %r9, 0
	std %r9, 304(%r11)
	std %r9, 312(%r11)
	std %r9, 320(%r11)
	std %r9, 328(%r11)
	std %r9, 336(%r11)
	std %r9, 344(%r11)
	std %r9, 352(%r11)
	std %r9, 360(%r11)
	std %r9, 368(%r11)
	ld %r6, 208(%r11)
	li %r9, 66
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 370
	subf %r5, %r6, %r5
	ld %r4, 184(%r11)
20:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	addi %r11, %r1, 0
	li %r9, 0
	std %r9, 376(%r11)
	std %r9, 384(%r11)
	std %r9, 392(%r11)
	std %r9, 400(%r11)
	std %r9, 408(%r11)
	std %r9, 416(%r11)
	std %r9, 424(%r11)
	std %r9, 432(%r11)
	std %r9, 440(%r11)
	ld %r6, 208(%r11)
	addi %r5, %r1, 441
	subf %r5, %r6, %r5
	ld %r4, 184(%r11)
21:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r7, %r1, 376
	li %r9, 58
	ldbrx %r8, %r7, %r9
	std %r8, 2560(%r3)
	li %r9, 50
	ldbrx %r8, %r7, %r9
	std %r8, 2568(%r3)
	li %r9, 42
	ldbrx %r8, %r7, %r9
	std %r8, 2576(%r3)
	li %r9, 34
	ldbrx %r8, %r7, %r9
	std %r8, 2584(%r3)
	li %r9, 26
	ldbrx %r8, %r7, %r9
	std %r8, 2592(%r3)
	li %r9, 18
	ldbrx %r8, %r7, %r9
	std %r8, 2600(%r3)
	li %r9, 10
	ldbrx %r8, %r7, %r9
	std %r8, 2608(%r3)
	li %r9, 2
	ldbrx %r8, %r7, %r9
	std %r8, 2616(%r3)
	li %r9, 0
	ldbrx %r8, %r7, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2624(%r3)
	ld %r4, 2560(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2568(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2560(%r3)
	ld %r4, 2568(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2576(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2568(%r3)
	ld %r4, 2576(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2584(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2576(%r3)
	ld %r4, 2584(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2592(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2584(%r3)
	ld %r4, 2592(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2600(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2592(%r3)
	ld %r4, 2600(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2608(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2600(%r3)
	ld %r4, 2608(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2616(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2608(%r3)
	ld %r4, 2616(%r3)
	rldicl %r4, %r4, 63, 1
	ld %r8, 2624(%r3)
	rldicr %r8, %r8, 63, 0
	or %r4, %r4, %r8
	std %r4, 2616(%r3)
	ld %r4, 2624(%r3)
	rldicl %r4, %r4, 63, 1
	std %r4, 2624(%r3)
	li %r10, 0
	addi %r10, %r10, -1
	ld %r4, 2560(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r7, %r6
	ld %r4, 2568(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r7, %r6
	ld %r4, 2576(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r7, %r6
	ld %r4, 2584(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r7, %r6
	ld %r4, 2592(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r7, %r6
	ld %r4, 2600(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r7, %r6
	ld %r4, 2608(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r7, %r6
	ld %r4, 2616(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r7, %r6
	ld %r4, 2624(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r7)
	stb %r4, 1(%r7)
	addi %r4, %r1, 96
	li %r5, 64
	li %r6, 1
22:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	addi %r4, %r1, 32
	li %r5, 64
	li %r6, 0
23:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2257(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2261(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2265(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2269(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 48(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 52(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 56(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 60(%r10)
	stw %r8, 2317(%r9)
	lbz %r8, 64(%r10)
	stb %r8, 2321(%r9)
	lbz %r8, 65(%r10)
	stb %r8, 2322(%r9)
	lwz %r8, 304(%r11)
	stw %r8, 2323(%r9)
	lwz %r8, 308(%r11)
	stw %r8, 2327(%r9)
	lwz %r8, 312(%r11)
	stw %r8, 2331(%r9)
	lwz %r8, 316(%r11)
	stw %r8, 2335(%r9)
	lwz %r8, 320(%r11)
	stw %r8, 2339(%r9)
	lwz %r8, 324(%r11)
	stw %r8, 2343(%r9)
	lwz %r8, 328(%r11)
	stw %r8, 2347(%r9)
	lwz %r8, 332(%r11)
	stw %r8, 2351(%r9)
	lwz %r8, 336(%r11)
	stw %r8, 2355(%r9)
	lwz %r8, 340(%r11)
	stw %r8, 2359(%r9)
	lwz %r8, 344(%r11)
	stw %r8, 2363(%r9)
	lwz %r8, 348(%r11)
	stw %r8, 2367(%r9)
	lwz %r8, 352(%r11)
	stw %r8, 2371(%r9)
	lwz %r8, 356(%r11)
	stw %r8, 2375(%r9)
	lwz %r8, 360(%r11)
	stw %r8, 2379(%r9)
	lwz %r8, 364(%r11)
	stw %r8, 2383(%r9)
	lbz %r8, 368(%r11)
	stb %r8, 2387(%r9)
	lbz %r8, 369(%r11)
	stb %r8, 2388(%r9)
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r3, 2256
	li %r6, 133
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 133
	addi %r6, %r1, 32
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 0
	addi %r5, %r12, 3072
	li %r6, 384
24:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 24b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 1
	stb %r8, 2256(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 3072
	addi %r5, %r12, 0
	li %r6, 384
25:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r3, 2256
	li %r6, 133
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 133
	addi %r6, %r1, 32
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 0
	addi %r5, %r12, 3072
	li %r6, 384
26:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 26b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 168(%r11)
27:
	li %r9, 0
	addi %r11, %r1, 0
	std %r9, 160(%r11)
28:
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 3072
	addi %r5, %r12, 0
	li %r6, 384
29:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 29b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	addi %r4, %r1, 96
	addi %r5, %r1, 448
	ld %r9, 160(%r11)
	add %r5, %r5, %r9
	ld %r6, 208(%r11)
210:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 210b
	addi %r11, %r1, 0
	ld %r9, 160(%r11)
	ld %r10, 208(%r11)
	add %r9, %r9, %r10
	std %r9, 160(%r11)
	li %r10, 66
	subfc %r12, %r10, %r9
	subfe %r12, %r12, %r12
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r7, %r1, 448
	li %r9, 58
	ldbrx %r8, %r7, %r9
	std %r8, 2560(%r3)
	li %r9, 50
	ldbrx %r8, %r7, %r9
	std %r8, 2568(%r3)
	li %r9, 42
	ldbrx %r8, %r7, %r9
	std %r8, 2576(%r3)
	li %r9, 34
	ldbrx %r8, %r7, %r9
	std %r8, 2584(%r3)
	li %r9, 26
	ldbrx %r8, %r7, %r9
	std %r8, 2592(%r3)
	li %r9, 18
	ldbrx %r8, %r7, %r9
	std %r8, 2600(%r3)
	li %r9, 10
	ldbrx %r8, %r7, %r9
	std %r8, 2608(%r3)
	li %r9, 2
	ldbrx %r8, %r7, %r9
	std %r8, 2616(%r3)
	li %r9, 0
	ldbrx %r8, %r7, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2624(%r3)
	ld %r4, 2560(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2568(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2560(%r3)
	ld %r4, 2568(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2576(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2568(%r3)
	ld %r4, 2576(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2584(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2576(%r3)
	ld %r4, 2584(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2592(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2584(%r3)
	ld %r4, 2592(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2600(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2592(%r3)
	ld %r4, 2600(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2608(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2600(%r3)
	ld %r4, 2608(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2616(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2608(%r3)
	ld %r4, 2616(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2624(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2616(%r3)
	ld %r4, 2624(%r3)
	rldicl %r4, %r4, 57, 7
	std %r4, 2624(%r3)
	li %r10, 0
	addi %r10, %r10, -1
	ld %r4, 2560(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r7, %r6
	ld %r4, 2568(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r7, %r6
	ld %r4, 2576(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r7, %r6
	ld %r4, 2584(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r7, %r6
	ld %r4, 2592(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r7, %r6
	ld %r4, 2600(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r7, %r6
	ld %r4, 2608(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r7, %r6
	ld %r4, 2616(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r7, %r6
	ld %r4, 2624(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r7)
	stb %r4, 1(%r7)
	addi %r11, %r1, 0
	ld %r3, 200(%r11)
	ld %r4, 192(%r11)
	addi %r5, %r1, 376
	addi %r6, %r1, 448
	ld %r7, 176(%r11)
	bl {vg_ecdsa_p521_sign_k}
	addi %r11, %r1, 0
	ld %r9, 168(%r11)
	addi %r9, %r9, -1
	std %r9, 168(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 211f
	li %r12, 0
	b 212f
211:
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r3, 2256
	li %r6, 1
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 1
	addi %r6, %r1, 32
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 0
	addi %r5, %r12, 3072
	li %r6, 384
213:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r3, 176(%r11)
	addi %r4, %r3, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r3, 384
	ld %r12, 224(%r11)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r12, 1
212:
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	addi %r4, %r1, 32
	li %r5, 128
	li %r6, 0
214:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	addi %r4, %r1, 232
	li %r5, 360
	li %r6, 0
215:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	addi %r1, %r1, 592
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -784(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	addi %r1, %r1, 784
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
