// The functions of `src/internal/vg_mlkem_compress_encode.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_compress_encode:
	rlwinm %r4, %r4, 0, 0, 31
	addi %r7, %r4, -1
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	addi %r7, %r4, -4
	cmplwi %cr0, %r7, 0
	beq %cr0, 22f
	lis %r10, 3
	ori %r10, %r10, 65472
	lis %r9, 2
	ori %r9, %r9, 30199
	li %r11, 64
24:
	li %r8, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 10, 54
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 20, 44
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 30, 34
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
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
	addi %r3, %r3, 16
	addi %r5, %r5, 5
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
	lis %r10, 3
	ori %r10, %r10, 65472
	li %r9, 2520
	li %r11, 128
25:
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 60, 3
	rldicl %r8, %r7, 4, 60
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 8, 56
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r3, %r3, 8
	addi %r5, %r5, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
23:
	b 21f
20:
	lis %r10, 3
	ori %r10, %r10, 65472
	li %r9, 315
	li %r11, 32
26:
	li %r8, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 2, 62
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 3, 61
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 4, 60
	add %r8, %r8, %r7
	lwz %r7, 16(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 5, 59
	add %r8, %r8, %r7
	lwz %r7, 20(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 6, 58
	add %r8, %r8, %r7
	lwz %r7, 24(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 7, 57
	add %r8, %r8, %r7
	lwz %r7, 28(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 8, 56
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r3, %r3, 32
	addi %r5, %r5, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
21:
	blr
