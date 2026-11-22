// The functions of `src/ecdsa_p192.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_verify:
	stdu %r1, -112(%r1)
	addi %r8, %r1, 32
	li %r11, 24
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
	addi %r10, %r8, 24
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
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 808(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 816(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 824(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 832(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 840(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 848(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 872(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P192_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P192_FRAME_CONSTS}
	mtlr %r11
	li %r31, 51
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
	std %r4, 1120(%r3)
	or %r12, %r5, %r5
	li %r31, 24
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 808(%r4)
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
	li %r31, 24
27:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 352(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4288(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4289(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4290(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4291(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4292(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4293(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4294(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4295(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r31, 24
28:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 376(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4480(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4481(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4482(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4483(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4484(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4485(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4486(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4487(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	addi %r6, %r12, 24
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 784(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 792(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 800(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1000(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1004(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1012(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1016(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1020(%r3)
	lis %r11, -22813
	ori %r11, %r11, 15000
	stw %r11, 1024(%r3)
	lis %r11, 25305
	ori %r11, %r11, 58374
	stw %r11, 1028(%r3)
	lis %r11, 6407
	ori %r11, %r11, 27362
	stw %r11, 1032(%r3)
	lis %r11, 29313
	ori %r11, %r11, 52658
	stw %r11, 1036(%r3)
	lis %r11, 22464
	ori %r11, %r11, 45361
	stw %r11, 1040(%r3)
	lis %r11, 29640
	ori %r11, %r11, 61125
	stw %r11, 1044(%r3)
	addi %r6, %r14, 1
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 872(%r3)
	addi %r6, %r6, 24
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 928(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 936(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 944(%r3)
	lbz %r4, 0(%r14)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 856(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 860(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 864(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 868(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 872(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 876(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 928(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 932(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 936(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 940(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 944(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 948(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	bl {vg_p192_validate}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 808(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 812(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 816(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 820(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 824(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 828(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 808(%r3)
	ld %r4, 816(%r3)
	or %r5, %r5, %r4
	ld %r4, 824(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 784(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 788(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 792(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 796(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 800(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 804(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 784(%r3)
	ld %r4, 792(%r3)
	or %r5, %r5, %r4
	ld %r4, 800(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r4, 952
	li %r5, 784
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	bl {vg_p192_inv_mod_n}
	li %r4, 1024
	li %r5, 832
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1000
	li %r5, 808
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1048
	li %r5, 1024
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	li %r4, 1072
	li %r5, 1000
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	li %r4, 880
	li %r5, 1048
	li %r6, 160
	bl {vg_p192_mul_mod_n}
	li %r4, 904
	li %r5, 1072
	li %r6, 160
	bl {vg_p192_mul_mod_n}
	li %r31, 24
29:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 880(%r4)
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
	li %r31, 24
210:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 904(%r4)
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
	bne %cr0, 210b
	ld %r4, 208(%r3)
	std %r4, 3648(%r3)
	ld %r4, 216(%r3)
	std %r4, 3656(%r3)
	ld %r4, 224(%r3)
	std %r4, 3664(%r3)
	ld %r4, 232(%r3)
	std %r4, 3672(%r3)
	ld %r4, 240(%r3)
	std %r4, 3680(%r3)
	ld %r4, 248(%r3)
	std %r4, 3688(%r3)
	ld %r4, 256(%r3)
	std %r4, 3504(%r3)
	ld %r4, 264(%r3)
	std %r4, 3512(%r3)
	ld %r4, 272(%r3)
	std %r4, 3520(%r3)
	ld %r4, 280(%r3)
	std %r4, 3528(%r3)
	ld %r4, 288(%r3)
	std %r4, 3536(%r3)
	ld %r4, 296(%r3)
	std %r4, 3544(%r3)
	ld %r4, 184(%r3)
	std %r4, 3552(%r3)
	ld %r4, 192(%r3)
	std %r4, 3560(%r3)
	ld %r4, 200(%r3)
	std %r4, 3568(%r3)
	ld %r4, 976(%r3)
	std %r4, 3576(%r3)
	ld %r4, 984(%r3)
	std %r4, 3584(%r3)
	ld %r4, 992(%r3)
	std %r4, 3592(%r3)
	ld %r4, 1096(%r3)
	std %r4, 3600(%r3)
	ld %r4, 1104(%r3)
	std %r4, 3608(%r3)
	ld %r4, 1112(%r3)
	std %r4, 3616(%r3)
	ld %r4, 184(%r3)
	std %r4, 3624(%r3)
	ld %r4, 192(%r3)
	std %r4, 3632(%r3)
	ld %r4, 200(%r3)
	std %r4, 3640(%r3)
	bl {vg_p192_point_add}
	ld %r4, 3432(%r3)
	std %r4, 808(%r3)
	ld %r4, 3440(%r3)
	std %r4, 816(%r3)
	ld %r4, 3448(%r3)
	std %r4, 824(%r3)
	ld %r4, 3456(%r3)
	std %r4, 832(%r3)
	ld %r4, 3464(%r3)
	std %r4, 840(%r3)
	ld %r4, 3472(%r3)
	std %r4, 848(%r3)
	ld %r4, 3480(%r3)
	std %r4, 856(%r3)
	ld %r4, 3488(%r3)
	std %r4, 864(%r3)
	ld %r4, 3496(%r3)
	std %r4, 872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 400(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 404(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 420(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 424(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 448(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 452(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 464(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 468(%r3)
	li %r31, 192
211:
	addi %r31, %r31, -1
	ld %r4, 400(%r3)
	std %r4, 3504(%r3)
	ld %r4, 408(%r3)
	std %r4, 3512(%r3)
	ld %r4, 416(%r3)
	std %r4, 3520(%r3)
	ld %r4, 424(%r3)
	std %r4, 3528(%r3)
	ld %r4, 432(%r3)
	std %r4, 3536(%r3)
	ld %r4, 440(%r3)
	std %r4, 3544(%r3)
	ld %r4, 448(%r3)
	std %r4, 3552(%r3)
	ld %r4, 456(%r3)
	std %r4, 3560(%r3)
	ld %r4, 464(%r3)
	std %r4, 3568(%r3)
	bl {vg_p192_point_double}
	ld %r4, 3432(%r3)
	std %r4, 3504(%r3)
	ld %r4, 3440(%r3)
	std %r4, 3512(%r3)
	ld %r4, 3448(%r3)
	std %r4, 3520(%r3)
	ld %r4, 3456(%r3)
	std %r4, 3528(%r3)
	ld %r4, 3464(%r3)
	std %r4, 3536(%r3)
	ld %r4, 3472(%r3)
	std %r4, 3544(%r3)
	ld %r4, 3480(%r3)
	std %r4, 3552(%r3)
	ld %r4, 3488(%r3)
	std %r4, 3560(%r3)
	ld %r4, 3496(%r3)
	std %r4, 3568(%r3)
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 136(%r3)
	ld %r5, 256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 144(%r3)
	ld %r5, 264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 152(%r3)
	ld %r5, 272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 184(%r3)
	ld %r5, 280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	ld %r4, 192(%r3)
	ld %r5, 288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 576(%r3)
	ld %r4, 200(%r3)
	ld %r5, 296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 584(%r3)
	ld %r4, 136(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 592(%r3)
	ld %r4, 144(%r3)
	ld %r5, 192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 600(%r3)
	ld %r4, 152(%r3)
	ld %r5, 200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 976(%r3)
	ld %r5, 808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 472(%r3)
	ld %r4, 984(%r3)
	ld %r5, 816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 480(%r3)
	ld %r4, 992(%r3)
	ld %r5, 824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 488(%r3)
	ld %r4, 1096(%r3)
	ld %r5, 832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 496(%r3)
	ld %r4, 1104(%r3)
	ld %r5, 840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 504(%r3)
	ld %r4, 1112(%r3)
	ld %r5, 848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 512(%r3)
	ld %r4, 184(%r3)
	ld %r5, 856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 520(%r3)
	ld %r4, 192(%r3)
	ld %r5, 864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 528(%r3)
	ld %r4, 200(%r3)
	ld %r5, 872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 536(%r3)
	add %r4, %r3, %r31
	lbz %r4, 4672(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 544(%r3)
	ld %r5, 472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3576(%r3)
	ld %r4, 552(%r3)
	ld %r5, 480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3584(%r3)
	ld %r4, 560(%r3)
	ld %r5, 488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3592(%r3)
	ld %r4, 568(%r3)
	ld %r5, 496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3600(%r3)
	ld %r4, 576(%r3)
	ld %r5, 504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3608(%r3)
	ld %r4, 584(%r3)
	ld %r5, 512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3616(%r3)
	ld %r4, 592(%r3)
	ld %r5, 520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3624(%r3)
	ld %r4, 600(%r3)
	ld %r5, 528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3632(%r3)
	ld %r4, 608(%r3)
	ld %r5, 536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3640(%r3)
	bl {vg_p192_point_add}
	ld %r4, 3432(%r3)
	std %r4, 400(%r3)
	ld %r4, 3440(%r3)
	std %r4, 408(%r3)
	ld %r4, 3448(%r3)
	std %r4, 416(%r3)
	ld %r4, 3456(%r3)
	std %r4, 424(%r3)
	ld %r4, 3464(%r3)
	std %r4, 432(%r3)
	ld %r4, 3472(%r3)
	std %r4, 440(%r3)
	ld %r4, 3480(%r3)
	std %r4, 448(%r3)
	ld %r4, 3488(%r3)
	std %r4, 456(%r3)
	ld %r4, 3496(%r3)
	std %r4, 464(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	bl {vg_p192_inv_mod_p}
	li %r4, 880
	li %r5, 400
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 904
	li %r5, 880
	li %r6, 160
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 904
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1024
	li %r5, 976
	li %r6, 1000
	bl {vg_p192_sub_mod_n}
	ld %r5, 448(%r3)
	ld %r4, 456(%r3)
	or %r5, %r5, %r4
	ld %r4, 464(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r5, 1024(%r3)
	ld %r4, 1032(%r3)
	or %r5, %r5, %r4
	ld %r4, 1040(%r3)
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
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r10, 1120(%r3)
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
	blr

vg_ecdsa_p192_sign:
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
	li %r9, 24
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 328
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
	addi %r9, %r1, 304
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 252
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 248
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 244
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 240
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 236
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 232
	stwbrx %r7, %r11, %r12
	addi %r4, %r1, 96
	li %r5, 64
	li %r6, 1
21:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 21b
	addi %r4, %r1, 32
	li %r5, 64
	li %r6, 0
22:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
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
	lwz %r8, 232(%r11)
	stw %r8, 2281(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2285(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2289(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2293(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2301(%r9)
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
	li %r6, 49
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
	addi %r5, %r5, 49
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
23:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
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
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r3, 2256
	li %r6, 49
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
	addi %r5, %r5, 49
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
26:
	li %r9, 0
	addi %r11, %r1, 0
	std %r9, 160(%r11)
27:
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r4, %r12, 3072
	addi %r5, %r12, 0
	li %r6, 384
28:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 28b
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
29:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 29b
	addi %r11, %r1, 0
	ld %r9, 160(%r11)
	ld %r10, 208(%r11)
	add %r9, %r9, %r10
	std %r9, 160(%r11)
	li %r10, 24
	subfc %r12, %r10, %r9
	subfe %r12, %r12, %r12
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	addi %r11, %r1, 0
	ld %r3, 200(%r11)
	ld %r4, 192(%r11)
	addi %r5, %r1, 304
	addi %r6, %r1, 448
	ld %r7, 176(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 168(%r11)
	addi %r9, %r9, -1
	std %r9, 168(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 210f
	li %r12, 0
	b 211f
210:
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
212:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 212b
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
211:
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	addi %r4, %r1, 32
	li %r5, 128
	li %r6, 0
213:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	addi %r4, %r1, 232
	li %r5, 360
	li %r6, 0
214:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
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
