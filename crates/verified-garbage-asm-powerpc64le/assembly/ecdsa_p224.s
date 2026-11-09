// The functions of `src/ecdsa_p224.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p224_verify:
	stdu %r1, -112(%r1)
	addi %r8, %r1, 32
	li %r11, 28
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
	addi %r10, %r8, 28
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
	li %r9, 20
	ldbrx %r8, %r5, %r9
	std %r8, 1056(%r3)
	li %r9, 12
	ldbrx %r8, %r5, %r9
	std %r8, 1064(%r3)
	li %r9, 4
	ldbrx %r8, %r5, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1080(%r3)
	li %r9, 20
	ldbrx %r8, %r4, %r9
	std %r8, 1088(%r3)
	li %r9, 12
	ldbrx %r8, %r4, %r9
	std %r8, 1096(%r3)
	li %r9, 4
	ldbrx %r8, %r4, %r9
	std %r8, 1104(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1112(%r3)
	li %r9, 20
	ldbrx %r8, %r4, %r9
	std %r8, 1120(%r3)
	li %r9, 12
	ldbrx %r8, %r4, %r9
	std %r8, 1128(%r3)
	li %r9, 4
	ldbrx %r8, %r4, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1144(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 64(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 68(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 72(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 76(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 80(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 84(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 88(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 92(%r3)
	lis %r11, 23644
	ori %r11, %r11, 10813
	stw %r11, 96(%r3)
	lis %r11, 5085
	ori %r11, %r11, 10565
	stw %r11, 100(%r3)
	lis %r11, -8008
	ori %r11, %r11, 61502
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 5794
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 120(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 124(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 160(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 164(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 168(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 172(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 176(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 180(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 188(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 192(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 196(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 204(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 224(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 228(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 232(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 252(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 256(%r3)
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 264(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 268(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 272(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 276(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 284(%r3)
	lis %r11, 11073
	ori %r11, %r11, 3430
	stw %r11, 288(%r3)
	lis %r11, -18886
	ori %r11, %r11, 27107
	stw %r11, 292(%r3)
	lis %r11, 26320
	ori %r11, %r11, 14642
	stw %r11, 296(%r3)
	lis %r11, 12656
	ori %r11, %r11, 18652
	stw %r11, 300(%r3)
	lis %r11, 22775
	ori %r11, %r11, 33779
	stw %r11, 304(%r3)
	lis %r11, -18068
	ori %r11, %r11, 12234
	stw %r11, 308(%r3)
	lis %r11, 32576
	ori %r11, %r11, 36537
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 27914
	ori %r11, %r11, 19178
	stw %r11, 320(%r3)
	lis %r11, -17264
	ori %r11, %r11, 21030
	stw %r11, 324(%r3)
	lis %r11, 24600
	ori %r11, %r11, 49066
	stw %r11, 328(%r3)
	lis %r11, -31451
	ori %r11, %r11, 38710
	stw %r11, 332(%r3)
	lis %r11, -1685
	ori %r11, %r11, 60421
	stw %r11, 336(%r3)
	lis %r11, 28115
	ori %r11, %r11, 44955
	stw %r11, 340(%r3)
	lis %r11, -24037
	ori %r11, %r11, 24160
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, -4109
	ori %r11, %r11, 60904
	stw %r11, 352(%r3)
	lis %r11, 11996
	ori %r11, %r11, 41445
	stw %r11, 356(%r3)
	lis %r11, 1331
	ori %r11, %r11, 23147
	stw %r11, 360(%r3)
	lis %r11, -1843
	ori %r11, %r11, 26411
	stw %r11, 364(%r3)
	lis %r11, 991
	ori %r11, %r11, 59512
	stw %r11, 368(%r3)
	lis %r11, -20823
	ori %r11, %r11, 50606
	stw %r11, 372(%r3)
	lis %r11, 24903
	ori %r11, %r11, 34545
	stw %r11, 376(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 380(%r3)
	lis %r11, 24401
	ori %r11, %r11, 32021
	stw %r11, 384(%r3)
	lis %r11, 10644
	ori %r11, %r11, 31337
	stw %r11, 388(%r3)
	lis %r11, 12758
	ori %r11, %r11, 16203
	stw %r11, 392(%r3)
	lis %r11, -21560
	ori %r11, %r11, 65369
	stw %r11, 396(%r3)
	lis %r11, -9871
	ori %r11, %r11, 18518
	stw %r11, 400(%r3)
	lis %r11, 27345
	ori %r11, %r11, 24444
	stw %r11, 404(%r3)
	lis %r11, -19991
	ori %r11, %r11, 31073
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, -23645
	ori %r11, %r11, 54723
	stw %r11, 420(%r3)
	lis %r11, -5086
	ori %r11, %r11, 54970
	stw %r11, 424(%r3)
	lis %r11, 8007
	ori %r11, %r11, 4033
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 59741
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
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 452(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 456(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 460(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 464(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 468(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 472(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 476(%r3)
	lis %r11, 23644
	ori %r11, %r11, 10811
	stw %r11, 480(%r3)
	lis %r11, 5085
	ori %r11, %r11, 10565
	stw %r11, 484(%r3)
	lis %r11, -8008
	ori %r11, %r11, 61502
	stw %r11, 488(%r3)
	lis %r11, -1
	ori %r11, %r11, 5794
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 504(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 508(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 516(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 520(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 524(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 528(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 532(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 536(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 540(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 544(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 548(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 560(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 564(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 568(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 572(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 576(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 580(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 584(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 588(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 592(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 596(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 600(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 604(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1472(%r3)
	or %r12, %r5, %r5
	li %r31, 32
25:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1056(%r4)
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
	bne %cr0, 25b
	li %r31, 32
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 448(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4352(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4353(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4354(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4355(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4356(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4357(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4358(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4359(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r31, 32
27:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 480(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4608(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4609(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4610(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4611(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4612(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4613(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4614(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4615(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	addi %r6, %r12, 28
	li %r9, 20
	ldbrx %r8, %r6, %r9
	std %r8, 1024(%r3)
	li %r9, 12
	ldbrx %r8, %r6, %r9
	std %r8, 1032(%r3)
	li %r9, 4
	ldbrx %r8, %r6, %r9
	std %r8, 1040(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1048(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1312(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1316(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1320(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1324(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1328(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1332(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1340(%r3)
	lis %r11, 25536
	ori %r11, %r11, 22989
	stw %r11, 1344(%r3)
	lis %r11, -6296
	ori %r11, %r11, 52726
	stw %r11, 1348(%r3)
	lis %r11, -13072
	ori %r11, %r11, 4880
	stw %r11, 1352(%r3)
	lis %r11, 4218
	ori %r11, %r11, 49907
	stw %r11, 1356(%r3)
	lis %r11, -14254
	ori %r11, %r11, 33105
	stw %r11, 1360(%r3)
	lis %r11, 15822
	ori %r11, %r11, 47768
	stw %r11, 1364(%r3)
	lis %r11, 32704
	ori %r11, %r11, 12179
	stw %r11, 1368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1372(%r3)
	addi %r6, %r14, 1
	li %r9, 20
	ldbrx %r8, %r6, %r9
	std %r8, 1120(%r3)
	li %r9, 12
	ldbrx %r8, %r6, %r9
	std %r8, 1128(%r3)
	li %r9, 4
	ldbrx %r8, %r6, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1144(%r3)
	addi %r6, %r6, 28
	li %r9, 20
	ldbrx %r8, %r6, %r9
	std %r8, 1216(%r3)
	li %r9, 12
	ldbrx %r8, %r6, %r9
	std %r8, 1224(%r3)
	li %r9, 4
	ldbrx %r8, %r6, %r9
	std %r8, 1232(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1240(%r3)
	lbz %r4, 0(%r14)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1120(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1124(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1128(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1132(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1136(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1140(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1144(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1148(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1216(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1220(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1224(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1228(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1232(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1236(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1240(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1244(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r4, 1152
	li %r5, 1120
	li %r6, 1312
	bl {vg_p224_mul_mod_p}
	li %r4, 1184
	li %r5, 1216
	li %r6, 1312
	bl {vg_p224_mul_mod_p}
	li %r4, 1248
	li %r5, 1184
	li %r6, 1184
	bl {vg_p224_mul_mod_p}
	li %r4, 1376
	li %r5, 1152
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1408
	li %r5, 1376
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1376
	li %r5, 256
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1280
	li %r5, 1408
	li %r6, 1376
	bl {vg_p224_add_mod_p}
	li %r4, 1408
	li %r5, 1280
	li %r6, 1344
	bl {vg_p224_add_mod_p}
	li %r4, 1376
	li %r5, 1248
	li %r6, 1408
	bl {vg_p224_sub_mod_p}
	ld %r5, 1376(%r3)
	ld %r4, 1384(%r3)
	or %r5, %r5, %r4
	ld %r4, 1392(%r3)
	or %r5, %r5, %r4
	ld %r4, 1400(%r3)
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
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r10, 1472(%r3)
	ld %r4, 320(%r3)
	ld %r5, 1152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1280(%r3)
	ld %r4, 328(%r3)
	ld %r5, 1160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1288(%r3)
	ld %r4, 336(%r3)
	ld %r5, 1168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1296(%r3)
	ld %r4, 344(%r3)
	ld %r5, 1176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1304(%r3)
	ld %r4, 352(%r3)
	ld %r5, 1184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1440(%r3)
	ld %r4, 360(%r3)
	ld %r5, 1192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1448(%r3)
	ld %r4, 368(%r3)
	ld %r5, 1200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 376(%r3)
	ld %r5, 1208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1056(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1060(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1064(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1068(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1072(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1076(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1080(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1084(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1056(%r3)
	ld %r4, 1064(%r3)
	or %r5, %r5, %r4
	ld %r4, 1072(%r3)
	or %r5, %r5, %r4
	ld %r4, 1080(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1024(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1028(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1032(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1036(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1040(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1044(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1048(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1052(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1024(%r3)
	ld %r4, 1032(%r3)
	or %r5, %r5, %r4
	ld %r4, 1040(%r3)
	or %r5, %r5, %r4
	ld %r4, 1048(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r4, 1248
	li %r5, 1024
	li %r6, 384
	bl {vg_p224_mul_mod_n}
	ld %r4, 1248(%r3)
	std %r4, 608(%r3)
	ld %r4, 1256(%r3)
	std %r4, 616(%r3)
	ld %r4, 1264(%r3)
	std %r4, 624(%r3)
	ld %r4, 1272(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 1248
	li %r6, 1248
	bl {vg_p224_mul_mod_n}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_p224_mul_mod_n}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
210:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
211:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
212:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
213:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
214:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
218:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
221:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
222:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
223:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
226:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
227:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
229:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
230:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
231:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 7
235:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p224_mul_mod_n}
	li %r31, 4
236:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p224_mul_mod_n}
	li %r31, 7
237:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p224_mul_mod_n}
	li %r31, 1
238:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 9
239:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p224_mul_mod_n}
	li %r31, 1
240:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 7
241:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 10
242:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_n}
	li %r31, 1
243:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 8
244:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p224_mul_mod_n}
	li %r31, 3
245:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p224_mul_mod_n}
	li %r31, 4
246:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p224_mul_mod_n}
	li %r31, 5
247:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p224_mul_mod_n}
	li %r31, 5
248:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p224_mul_mod_n}
	li %r31, 2
249:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 6
250:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p224_mul_mod_n}
	li %r31, 5
251:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p224_mul_mod_n}
	li %r31, 1
252:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 7
253:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p224_mul_mod_n}
	li %r31, 1
254:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 7
255:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p224_mul_mod_n}
	li %r31, 2
256:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p224_mul_mod_n}
	li %r31, 6
257:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p224_mul_mod_n}
	li %r31, 3
258:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p224_mul_mod_n}
	li %r4, 1344
	li %r5, 1088
	li %r6, 384
	bl {vg_p224_mul_mod_n}
	li %r4, 1312
	li %r5, 1056
	li %r6, 384
	bl {vg_p224_mul_mod_n}
	li %r4, 1376
	li %r5, 1344
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	li %r4, 1408
	li %r5, 1312
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	li %r4, 1152
	li %r5, 1376
	li %r6, 192
	bl {vg_p224_mul_mod_n}
	li %r4, 1184
	li %r5, 1408
	li %r6, 192
	bl {vg_p224_mul_mod_n}
	li %r31, 32
259:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1152(%r4)
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
	bne %cr0, 259b
	lis %r11, 25536
	ori %r11, %r11, 22989
	stw %r11, 1344(%r3)
	lis %r11, -6296
	ori %r11, %r11, 52726
	stw %r11, 1348(%r3)
	lis %r11, -13072
	ori %r11, %r11, 4880
	stw %r11, 1352(%r3)
	lis %r11, 4218
	ori %r11, %r11, 49907
	stw %r11, 1356(%r3)
	lis %r11, -14254
	ori %r11, %r11, 33105
	stw %r11, 1360(%r3)
	lis %r11, 15822
	ori %r11, %r11, 47768
	stw %r11, 1364(%r3)
	lis %r11, 32704
	ori %r11, %r11, 12179
	stw %r11, 1368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1372(%r3)
	ld %r4, 320(%r3)
	std %r4, 3424(%r3)
	ld %r4, 328(%r3)
	std %r4, 3432(%r3)
	ld %r4, 336(%r3)
	std %r4, 3440(%r3)
	ld %r4, 344(%r3)
	std %r4, 3448(%r3)
	ld %r4, 352(%r3)
	std %r4, 3456(%r3)
	ld %r4, 360(%r3)
	std %r4, 3464(%r3)
	ld %r4, 368(%r3)
	std %r4, 3472(%r3)
	ld %r4, 376(%r3)
	std %r4, 3480(%r3)
	ld %r4, 224(%r3)
	std %r4, 3488(%r3)
	ld %r4, 232(%r3)
	std %r4, 3496(%r3)
	ld %r4, 240(%r3)
	std %r4, 3504(%r3)
	ld %r4, 248(%r3)
	std %r4, 3512(%r3)
	ld %r4, 256(%r3)
	std %r4, 3520(%r3)
	ld %r4, 264(%r3)
	std %r4, 3528(%r3)
	ld %r4, 272(%r3)
	std %r4, 3536(%r3)
	ld %r4, 280(%r3)
	std %r4, 3544(%r3)
	ld %r4, 288(%r3)
	std %r4, 3552(%r3)
	ld %r4, 296(%r3)
	std %r4, 3560(%r3)
	ld %r4, 304(%r3)
	std %r4, 3568(%r3)
	ld %r4, 312(%r3)
	std %r4, 3576(%r3)
	lis %r11, 5375
	ori %r11, %r11, 13033
	stw %r11, 512(%r3)
	lis %r11, 9672
	ori %r11, %r11, 7832
	stw %r11, 516(%r3)
	lis %r11, -21202
	ori %r11, %r11, 43436
	stw %r11, 520(%r3)
	lis %r11, 5434
	ori %r11, %r11, 4319
	stw %r11, 524(%r3)
	lis %r11, -18673
	ori %r11, %r11, 64408
	stw %r11, 528(%r3)
	lis %r11, 24481
	ori %r11, %r11, 47493
	stw %r11, 532(%r3)
	lis %r11, -9411
	ori %r11, %r11, 45676
	stw %r11, 536(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 540(%r3)
	lis %r11, -7499
	ori %r11, %r11, 15012
	stw %r11, 544(%r3)
	lis %r11, 1888
	ori %r11, %r11, 5272
	stw %r11, 548(%r3)
	lis %r11, 21870
	ori %r11, %r11, 54321
	stw %r11, 552(%r3)
	lis %r11, -3152
	ori %r11, %r11, 57524
	stw %r11, 556(%r3)
	lis %r11, -24762
	ori %r11, %r11, 7600
	stw %r11, 560(%r3)
	lis %r11, -15651
	ori %r11, %r11, 33467
	stw %r11, 564(%r3)
	lis %r11, 23147
	ori %r11, %r11, 50641
	stw %r11, 568(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 572(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 576(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 580(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 584(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 588(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 592(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 596(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 600(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 604(%r3)
	li %r31, 32
260:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -31
	cmpldi %cr0, %r6, 0
	beq %cr0, 261f
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
	b 262f
261:
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
262:
	addi %r9, %r9, -64
	rldicl %r4, %r9, 1, 63
	li %r5, 0
	subf %r4, %r4, %r5
	xor %r9, %r9, %r4
	subf %r9, %r4, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_P224_COMB}
	addi %r8, %r8, ({VG_P224_COMB}
	li %r4, 4096
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	li %r7, 1
263:
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 263b
	li %r4, 3424
	stxvd2x 32, %r3, %r4
	li %r4, 3440
	stxvd2x 33, %r3, %r4
	li %r4, 3456
	stxvd2x 34, %r3, %r4
	li %r4, 3472
	stxvd2x 35, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3488(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3500(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3504(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3508(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3516(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3456(%r3)
	ld %r5, 3488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 3496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 3504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 3512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
	ld %r4, 3488(%r3)
	ld %r5, 160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3488(%r3)
	ld %r4, 3496(%r3)
	ld %r5, 168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3496(%r3)
	ld %r4, 3504(%r3)
	ld %r5, 176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3504(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3512(%r3)
	li %r4, 704
	li %r5, 160
	li %r6, 3456
	bl {vg_p224_sub_mod_p}
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	addi %r10, %r4, -1
	ld %r4, 3456(%r3)
	ld %r5, 704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
	ld %r4, 512(%r3)
	std %r4, 3328(%r3)
	ld %r4, 520(%r3)
	std %r4, 3336(%r3)
	ld %r4, 528(%r3)
	std %r4, 3344(%r3)
	ld %r4, 536(%r3)
	std %r4, 3352(%r3)
	ld %r4, 544(%r3)
	std %r4, 3360(%r3)
	ld %r4, 552(%r3)
	std %r4, 3368(%r3)
	ld %r4, 560(%r3)
	std %r4, 3376(%r3)
	ld %r4, 568(%r3)
	std %r4, 3384(%r3)
	ld %r4, 576(%r3)
	std %r4, 3392(%r3)
	ld %r4, 584(%r3)
	std %r4, 3400(%r3)
	ld %r4, 592(%r3)
	std %r4, 3408(%r3)
	ld %r4, 600(%r3)
	std %r4, 3416(%r3)
	bl {vg_p224_point_add}
	ld %r4, 3232(%r3)
	std %r4, 512(%r3)
	ld %r4, 3240(%r3)
	std %r4, 520(%r3)
	ld %r4, 3248(%r3)
	std %r4, 528(%r3)
	ld %r4, 3256(%r3)
	std %r4, 536(%r3)
	ld %r4, 3264(%r3)
	std %r4, 544(%r3)
	ld %r4, 3272(%r3)
	std %r4, 552(%r3)
	ld %r4, 3280(%r3)
	std %r4, 560(%r3)
	ld %r4, 3288(%r3)
	std %r4, 568(%r3)
	ld %r4, 3296(%r3)
	std %r4, 576(%r3)
	ld %r4, 3304(%r3)
	std %r4, 584(%r3)
	ld %r4, 3312(%r3)
	std %r4, 592(%r3)
	ld %r4, 3320(%r3)
	std %r4, 600(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	ld %r4, 512(%r3)
	std %r4, 1376(%r3)
	ld %r4, 520(%r3)
	std %r4, 1384(%r3)
	ld %r4, 528(%r3)
	std %r4, 1392(%r3)
	ld %r4, 536(%r3)
	std %r4, 1400(%r3)
	ld %r4, 544(%r3)
	std %r4, 1408(%r3)
	ld %r4, 552(%r3)
	std %r4, 1416(%r3)
	ld %r4, 560(%r3)
	std %r4, 1424(%r3)
	ld %r4, 568(%r3)
	std %r4, 1432(%r3)
	ld %r4, 576(%r3)
	std %r4, 1248(%r3)
	ld %r4, 584(%r3)
	std %r4, 1256(%r3)
	ld %r4, 592(%r3)
	std %r4, 1264(%r3)
	ld %r4, 600(%r3)
	std %r4, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 516(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 520(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 524(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 528(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 532(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 536(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 540(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 544(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 548(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 560(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 564(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 568(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 572(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 576(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 580(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 584(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 588(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 592(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 596(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 600(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 604(%r3)
	li %r31, 32
264:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1184(%r4)
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
	bne %cr0, 264b
	ld %r4, 160(%r3)
	std %r4, 4864(%r3)
	ld %r4, 168(%r3)
	std %r4, 4872(%r3)
	ld %r4, 176(%r3)
	std %r4, 4880(%r3)
	ld %r4, 184(%r3)
	std %r4, 4888(%r3)
	ld %r4, 224(%r3)
	std %r4, 4896(%r3)
	ld %r4, 232(%r3)
	std %r4, 4904(%r3)
	ld %r4, 240(%r3)
	std %r4, 4912(%r3)
	ld %r4, 248(%r3)
	std %r4, 4920(%r3)
	ld %r4, 160(%r3)
	std %r4, 4928(%r3)
	ld %r4, 168(%r3)
	std %r4, 4936(%r3)
	ld %r4, 176(%r3)
	std %r4, 4944(%r3)
	ld %r4, 184(%r3)
	std %r4, 4952(%r3)
	ld %r4, 1280(%r3)
	std %r4, 4960(%r3)
	ld %r4, 1288(%r3)
	std %r4, 4968(%r3)
	ld %r4, 1296(%r3)
	std %r4, 4976(%r3)
	ld %r4, 1304(%r3)
	std %r4, 4984(%r3)
	ld %r4, 1440(%r3)
	std %r4, 4992(%r3)
	ld %r4, 1448(%r3)
	std %r4, 5000(%r3)
	ld %r4, 1456(%r3)
	std %r4, 5008(%r3)
	ld %r4, 1464(%r3)
	std %r4, 5016(%r3)
	ld %r4, 224(%r3)
	std %r4, 5024(%r3)
	ld %r4, 232(%r3)
	std %r4, 5032(%r3)
	ld %r4, 240(%r3)
	std %r4, 5040(%r3)
	ld %r4, 248(%r3)
	std %r4, 5048(%r3)
	ld %r4, 1280(%r3)
	std %r4, 608(%r3)
	ld %r4, 1288(%r3)
	std %r4, 616(%r3)
	ld %r4, 1296(%r3)
	std %r4, 624(%r3)
	ld %r4, 1304(%r3)
	std %r4, 632(%r3)
	ld %r4, 1440(%r3)
	std %r4, 640(%r3)
	ld %r4, 1448(%r3)
	std %r4, 648(%r3)
	ld %r4, 1456(%r3)
	std %r4, 656(%r3)
	ld %r4, 1464(%r3)
	std %r4, 664(%r3)
	ld %r4, 224(%r3)
	std %r4, 672(%r3)
	ld %r4, 232(%r3)
	std %r4, 680(%r3)
	ld %r4, 240(%r3)
	std %r4, 688(%r3)
	ld %r4, 248(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5056(%r3)
	ld %r4, 712(%r3)
	std %r4, 5064(%r3)
	ld %r4, 720(%r3)
	std %r4, 5072(%r3)
	ld %r4, 728(%r3)
	std %r4, 5080(%r3)
	ld %r4, 736(%r3)
	std %r4, 5088(%r3)
	ld %r4, 744(%r3)
	std %r4, 5096(%r3)
	ld %r4, 752(%r3)
	std %r4, 5104(%r3)
	ld %r4, 760(%r3)
	std %r4, 5112(%r3)
	ld %r4, 768(%r3)
	std %r4, 5120(%r3)
	ld %r4, 776(%r3)
	std %r4, 5128(%r3)
	ld %r4, 784(%r3)
	std %r4, 5136(%r3)
	ld %r4, 792(%r3)
	std %r4, 5144(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5152(%r3)
	ld %r4, 712(%r3)
	std %r4, 5160(%r3)
	ld %r4, 720(%r3)
	std %r4, 5168(%r3)
	ld %r4, 728(%r3)
	std %r4, 5176(%r3)
	ld %r4, 736(%r3)
	std %r4, 5184(%r3)
	ld %r4, 744(%r3)
	std %r4, 5192(%r3)
	ld %r4, 752(%r3)
	std %r4, 5200(%r3)
	ld %r4, 760(%r3)
	std %r4, 5208(%r3)
	ld %r4, 768(%r3)
	std %r4, 5216(%r3)
	ld %r4, 776(%r3)
	std %r4, 5224(%r3)
	ld %r4, 784(%r3)
	std %r4, 5232(%r3)
	ld %r4, 792(%r3)
	std %r4, 5240(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5248(%r3)
	ld %r4, 712(%r3)
	std %r4, 5256(%r3)
	ld %r4, 720(%r3)
	std %r4, 5264(%r3)
	ld %r4, 728(%r3)
	std %r4, 5272(%r3)
	ld %r4, 736(%r3)
	std %r4, 5280(%r3)
	ld %r4, 744(%r3)
	std %r4, 5288(%r3)
	ld %r4, 752(%r3)
	std %r4, 5296(%r3)
	ld %r4, 760(%r3)
	std %r4, 5304(%r3)
	ld %r4, 768(%r3)
	std %r4, 5312(%r3)
	ld %r4, 776(%r3)
	std %r4, 5320(%r3)
	ld %r4, 784(%r3)
	std %r4, 5328(%r3)
	ld %r4, 792(%r3)
	std %r4, 5336(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5344(%r3)
	ld %r4, 712(%r3)
	std %r4, 5352(%r3)
	ld %r4, 720(%r3)
	std %r4, 5360(%r3)
	ld %r4, 728(%r3)
	std %r4, 5368(%r3)
	ld %r4, 736(%r3)
	std %r4, 5376(%r3)
	ld %r4, 744(%r3)
	std %r4, 5384(%r3)
	ld %r4, 752(%r3)
	std %r4, 5392(%r3)
	ld %r4, 760(%r3)
	std %r4, 5400(%r3)
	ld %r4, 768(%r3)
	std %r4, 5408(%r3)
	ld %r4, 776(%r3)
	std %r4, 5416(%r3)
	ld %r4, 784(%r3)
	std %r4, 5424(%r3)
	ld %r4, 792(%r3)
	std %r4, 5432(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5440(%r3)
	ld %r4, 712(%r3)
	std %r4, 5448(%r3)
	ld %r4, 720(%r3)
	std %r4, 5456(%r3)
	ld %r4, 728(%r3)
	std %r4, 5464(%r3)
	ld %r4, 736(%r3)
	std %r4, 5472(%r3)
	ld %r4, 744(%r3)
	std %r4, 5480(%r3)
	ld %r4, 752(%r3)
	std %r4, 5488(%r3)
	ld %r4, 760(%r3)
	std %r4, 5496(%r3)
	ld %r4, 768(%r3)
	std %r4, 5504(%r3)
	ld %r4, 776(%r3)
	std %r4, 5512(%r3)
	ld %r4, 784(%r3)
	std %r4, 5520(%r3)
	ld %r4, 792(%r3)
	std %r4, 5528(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5536(%r3)
	ld %r4, 712(%r3)
	std %r4, 5544(%r3)
	ld %r4, 720(%r3)
	std %r4, 5552(%r3)
	ld %r4, 728(%r3)
	std %r4, 5560(%r3)
	ld %r4, 736(%r3)
	std %r4, 5568(%r3)
	ld %r4, 744(%r3)
	std %r4, 5576(%r3)
	ld %r4, 752(%r3)
	std %r4, 5584(%r3)
	ld %r4, 760(%r3)
	std %r4, 5592(%r3)
	ld %r4, 768(%r3)
	std %r4, 5600(%r3)
	ld %r4, 776(%r3)
	std %r4, 5608(%r3)
	ld %r4, 784(%r3)
	std %r4, 5616(%r3)
	ld %r4, 792(%r3)
	std %r4, 5624(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5632(%r3)
	ld %r4, 712(%r3)
	std %r4, 5640(%r3)
	ld %r4, 720(%r3)
	std %r4, 5648(%r3)
	ld %r4, 728(%r3)
	std %r4, 5656(%r3)
	ld %r4, 736(%r3)
	std %r4, 5664(%r3)
	ld %r4, 744(%r3)
	std %r4, 5672(%r3)
	ld %r4, 752(%r3)
	std %r4, 5680(%r3)
	ld %r4, 760(%r3)
	std %r4, 5688(%r3)
	ld %r4, 768(%r3)
	std %r4, 5696(%r3)
	ld %r4, 776(%r3)
	std %r4, 5704(%r3)
	ld %r4, 784(%r3)
	std %r4, 5712(%r3)
	ld %r4, 792(%r3)
	std %r4, 5720(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5728(%r3)
	ld %r4, 712(%r3)
	std %r4, 5736(%r3)
	ld %r4, 720(%r3)
	std %r4, 5744(%r3)
	ld %r4, 728(%r3)
	std %r4, 5752(%r3)
	ld %r4, 736(%r3)
	std %r4, 5760(%r3)
	ld %r4, 744(%r3)
	std %r4, 5768(%r3)
	ld %r4, 752(%r3)
	std %r4, 5776(%r3)
	ld %r4, 760(%r3)
	std %r4, 5784(%r3)
	ld %r4, 768(%r3)
	std %r4, 5792(%r3)
	ld %r4, 776(%r3)
	std %r4, 5800(%r3)
	ld %r4, 784(%r3)
	std %r4, 5808(%r3)
	ld %r4, 792(%r3)
	std %r4, 5816(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5824(%r3)
	ld %r4, 712(%r3)
	std %r4, 5832(%r3)
	ld %r4, 720(%r3)
	std %r4, 5840(%r3)
	ld %r4, 728(%r3)
	std %r4, 5848(%r3)
	ld %r4, 736(%r3)
	std %r4, 5856(%r3)
	ld %r4, 744(%r3)
	std %r4, 5864(%r3)
	ld %r4, 752(%r3)
	std %r4, 5872(%r3)
	ld %r4, 760(%r3)
	std %r4, 5880(%r3)
	ld %r4, 768(%r3)
	std %r4, 5888(%r3)
	ld %r4, 776(%r3)
	std %r4, 5896(%r3)
	ld %r4, 784(%r3)
	std %r4, 5904(%r3)
	ld %r4, 792(%r3)
	std %r4, 5912(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5920(%r3)
	ld %r4, 712(%r3)
	std %r4, 5928(%r3)
	ld %r4, 720(%r3)
	std %r4, 5936(%r3)
	ld %r4, 728(%r3)
	std %r4, 5944(%r3)
	ld %r4, 736(%r3)
	std %r4, 5952(%r3)
	ld %r4, 744(%r3)
	std %r4, 5960(%r3)
	ld %r4, 752(%r3)
	std %r4, 5968(%r3)
	ld %r4, 760(%r3)
	std %r4, 5976(%r3)
	ld %r4, 768(%r3)
	std %r4, 5984(%r3)
	ld %r4, 776(%r3)
	std %r4, 5992(%r3)
	ld %r4, 784(%r3)
	std %r4, 6000(%r3)
	ld %r4, 792(%r3)
	std %r4, 6008(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6016(%r3)
	ld %r4, 712(%r3)
	std %r4, 6024(%r3)
	ld %r4, 720(%r3)
	std %r4, 6032(%r3)
	ld %r4, 728(%r3)
	std %r4, 6040(%r3)
	ld %r4, 736(%r3)
	std %r4, 6048(%r3)
	ld %r4, 744(%r3)
	std %r4, 6056(%r3)
	ld %r4, 752(%r3)
	std %r4, 6064(%r3)
	ld %r4, 760(%r3)
	std %r4, 6072(%r3)
	ld %r4, 768(%r3)
	std %r4, 6080(%r3)
	ld %r4, 776(%r3)
	std %r4, 6088(%r3)
	ld %r4, 784(%r3)
	std %r4, 6096(%r3)
	ld %r4, 792(%r3)
	std %r4, 6104(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6112(%r3)
	ld %r4, 712(%r3)
	std %r4, 6120(%r3)
	ld %r4, 720(%r3)
	std %r4, 6128(%r3)
	ld %r4, 728(%r3)
	std %r4, 6136(%r3)
	ld %r4, 736(%r3)
	std %r4, 6144(%r3)
	ld %r4, 744(%r3)
	std %r4, 6152(%r3)
	ld %r4, 752(%r3)
	std %r4, 6160(%r3)
	ld %r4, 760(%r3)
	std %r4, 6168(%r3)
	ld %r4, 768(%r3)
	std %r4, 6176(%r3)
	ld %r4, 776(%r3)
	std %r4, 6184(%r3)
	ld %r4, 784(%r3)
	std %r4, 6192(%r3)
	ld %r4, 792(%r3)
	std %r4, 6200(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6208(%r3)
	ld %r4, 712(%r3)
	std %r4, 6216(%r3)
	ld %r4, 720(%r3)
	std %r4, 6224(%r3)
	ld %r4, 728(%r3)
	std %r4, 6232(%r3)
	ld %r4, 736(%r3)
	std %r4, 6240(%r3)
	ld %r4, 744(%r3)
	std %r4, 6248(%r3)
	ld %r4, 752(%r3)
	std %r4, 6256(%r3)
	ld %r4, 760(%r3)
	std %r4, 6264(%r3)
	ld %r4, 768(%r3)
	std %r4, 6272(%r3)
	ld %r4, 776(%r3)
	std %r4, 6280(%r3)
	ld %r4, 784(%r3)
	std %r4, 6288(%r3)
	ld %r4, 792(%r3)
	std %r4, 6296(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6304(%r3)
	ld %r4, 712(%r3)
	std %r4, 6312(%r3)
	ld %r4, 720(%r3)
	std %r4, 6320(%r3)
	ld %r4, 728(%r3)
	std %r4, 6328(%r3)
	ld %r4, 736(%r3)
	std %r4, 6336(%r3)
	ld %r4, 744(%r3)
	std %r4, 6344(%r3)
	ld %r4, 752(%r3)
	std %r4, 6352(%r3)
	ld %r4, 760(%r3)
	std %r4, 6360(%r3)
	ld %r4, 768(%r3)
	std %r4, 6368(%r3)
	ld %r4, 776(%r3)
	std %r4, 6376(%r3)
	ld %r4, 784(%r3)
	std %r4, 6384(%r3)
	ld %r4, 792(%r3)
	std %r4, 6392(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	ld %r4, 160(%r3)
	std %r4, 512(%r3)
	ld %r4, 168(%r3)
	std %r4, 520(%r3)
	ld %r4, 176(%r3)
	std %r4, 528(%r3)
	ld %r4, 184(%r3)
	std %r4, 536(%r3)
	ld %r4, 224(%r3)
	std %r4, 544(%r3)
	ld %r4, 232(%r3)
	std %r4, 552(%r3)
	ld %r4, 240(%r3)
	std %r4, 560(%r3)
	ld %r4, 248(%r3)
	std %r4, 568(%r3)
	ld %r4, 160(%r3)
	std %r4, 576(%r3)
	ld %r4, 168(%r3)
	std %r4, 584(%r3)
	ld %r4, 176(%r3)
	std %r4, 592(%r3)
	ld %r4, 184(%r3)
	std %r4, 600(%r3)
	li %r31, 64
265:
	addi %r31, %r31, -1
	li %r4, 608
	li %r5, 512
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 800
	li %r5, 576
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 640
	li %r5, 544
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 576
	li %r6, 160
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 608
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 864
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 896
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 704
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 704
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 736
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 864
	li %r6, 608
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 896
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 608
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 864
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 896
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 704
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 704
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 736
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 864
	li %r6, 608
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 896
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 512
	li %r5, 608
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 576
	li %r5, 800
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 544
	li %r5, 640
	li %r6, 160
	bl {vg_p224_add_mod_p}
	ld %r5, 576(%r3)
	ld %r4, 584(%r3)
	or %r5, %r5, %r4
	ld %r4, 592(%r3)
	or %r5, %r5, %r4
	ld %r4, 600(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	or %r10, %r5, %r5
	ld %r4, 224(%r3)
	ld %r5, 544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 232(%r3)
	ld %r5, 552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 240(%r3)
	ld %r5, 560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 248(%r3)
	ld %r5, 568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	rldicr %r4, %r31, 2, 61
	add %r4, %r3, %r4
	lbz %r9, 4099(%r4)
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 4864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 4872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 4880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 4888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 4896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 4904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 4912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 4920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 4928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 4936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 4944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 4952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 1
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 4960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 4968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 4976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 4984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 4992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 2
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 3
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 4
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 5
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 6
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 7
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 8
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 9
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 10
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 11
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 12
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 13
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 14
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 15
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 512
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 544
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 576
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 512
	li %r6, 544
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 544
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 512
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 512(%r3)
	ld %r4, 712(%r3)
	std %r4, 520(%r3)
	ld %r4, 720(%r3)
	std %r4, 528(%r3)
	ld %r4, 728(%r3)
	std %r4, 536(%r3)
	ld %r4, 736(%r3)
	std %r4, 544(%r3)
	ld %r4, 744(%r3)
	std %r4, 552(%r3)
	ld %r4, 752(%r3)
	std %r4, 560(%r3)
	ld %r4, 760(%r3)
	std %r4, 568(%r3)
	ld %r4, 768(%r3)
	std %r4, 576(%r3)
	ld %r4, 776(%r3)
	std %r4, 584(%r3)
	ld %r4, 784(%r3)
	std %r4, 592(%r3)
	ld %r4, 792(%r3)
	std %r4, 600(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 800
	li %r5, 1376
	li %r6, 512
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 1408
	li %r6, 544
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 1248
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 1376
	li %r6, 1408
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 512
	li %r6, 544
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 1376
	li %r6, 1248
	bl {vg_p224_add_mod_p}
	li %r4, 960
	li %r5, 512
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_p224_mul_mod_p}
	li %r4, 960
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_p224_sub_mod_p}
	li %r4, 960
	li %r5, 1408
	li %r6, 1248
	bl {vg_p224_add_mod_p}
	li %r4, 608
	li %r5, 544
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 256
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 288
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 672
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 832
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 288
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 960
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 896
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 960
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p224_add_mod_p}
	ld %r4, 608(%r3)
	std %r4, 512(%r3)
	ld %r4, 616(%r3)
	std %r4, 520(%r3)
	ld %r4, 624(%r3)
	std %r4, 528(%r3)
	ld %r4, 632(%r3)
	std %r4, 536(%r3)
	ld %r4, 640(%r3)
	std %r4, 544(%r3)
	ld %r4, 648(%r3)
	std %r4, 552(%r3)
	ld %r4, 656(%r3)
	std %r4, 560(%r3)
	ld %r4, 664(%r3)
	std %r4, 568(%r3)
	ld %r4, 672(%r3)
	std %r4, 576(%r3)
	ld %r4, 680(%r3)
	std %r4, 584(%r3)
	ld %r4, 688(%r3)
	std %r4, 592(%r3)
	ld %r4, 696(%r3)
	std %r4, 600(%r3)
	ld %r4, 576(%r3)
	std %r4, 608(%r3)
	ld %r4, 584(%r3)
	std %r4, 616(%r3)
	ld %r4, 592(%r3)
	std %r4, 624(%r3)
	ld %r4, 600(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 576
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 4
266:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
267:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
268:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
269:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
270:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
271:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
272:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
273:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
274:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
275:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
276:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
277:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
278:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
279:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
280:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
281:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
282:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
283:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
284:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
285:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
286:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
287:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
288:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
289:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
290:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
291:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
292:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
293:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
294:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
295:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 3
296:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r31, 5
297:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
298:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
299:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2100:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2101:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2102:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2103:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2103b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2104:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2104b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2105:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2105b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2106:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2106b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2107:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2107b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2108:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2108b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2109:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2109b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2110:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2110b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2111:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2111b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2112:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2112b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2113:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2113b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2114:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2114b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2115:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2115b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2116:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2116b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2117:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2117b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2118:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2118b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2119:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2119b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r31, 4
2120:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2120b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 1152
	li %r5, 512
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	li %r4, 1184
	li %r5, 1152
	li %r6, 192
	bl {vg_p224_mul_mod_p}
	li %r4, 1280
	li %r5, 1184
	li %r6, 384
	bl {vg_p224_mul_mod_n}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1312
	bl {vg_p224_sub_mod_n}
	ld %r5, 576(%r3)
	ld %r4, 584(%r3)
	or %r5, %r5, %r4
	ld %r4, 592(%r3)
	or %r5, %r5, %r4
	ld %r4, 600(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r5, 1344(%r3)
	ld %r4, 1352(%r3)
	or %r5, %r5, %r4
	ld %r4, 1360(%r3)
	or %r5, %r5, %r4
	ld %r4, 1368(%r3)
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
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r10, 1472(%r3)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	addi %r1, %r1, 112
	blr

vg_ecdsa_p224_sign:
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
	li %r9, 28
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 332
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
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, 23644
	ori %r12, %r12, 10813
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5085
	ori %r12, %r12, 10565
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -8008
	ori %r12, %r12, 61502
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 5794
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
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
	li %r8, 4
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
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 256
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 252
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 248
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 244
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 240
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 236
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
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
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2285(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2289(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2293(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2309(%r9)
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
	li %r6, 57
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
	addi %r5, %r5, 57
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
	li %r6, 57
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
	addi %r5, %r5, 57
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
	li %r10, 28
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
	bl {vg_ecdsa_p224_sign_k}
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
	blr
