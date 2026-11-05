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
	ld %r4, 416(%r3)
	std %r4, 992(%r3)
	ld %r4, 424(%r3)
	std %r4, 1000(%r3)
	ld %r4, 432(%r3)
	std %r4, 1008(%r3)
	ld %r4, 440(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
28:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_n}
	li %r4, 1024
	li %r5, 992
	li %r6, 1248
	bl {vg_p224_mul_mod_n}
	add %r4, %r3, %r31
	lbz %r4, 4608(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 992(%r3)
	ld %r5, 1024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 1032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 1040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 1048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
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
	ld %r4, 1152(%r3)
	std %r4, 1056(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1064(%r3)
	ld %r4, 1168(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1176(%r3)
	std %r4, 1080(%r3)
	ld %r4, 320(%r3)
	std %r4, 512(%r3)
	ld %r4, 328(%r3)
	std %r4, 520(%r3)
	ld %r4, 336(%r3)
	std %r4, 528(%r3)
	ld %r4, 344(%r3)
	std %r4, 536(%r3)
	ld %r4, 352(%r3)
	std %r4, 544(%r3)
	ld %r4, 360(%r3)
	std %r4, 552(%r3)
	ld %r4, 368(%r3)
	std %r4, 560(%r3)
	ld %r4, 376(%r3)
	std %r4, 568(%r3)
	bl {vg_p224_mul}
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
	ld %r4, 1184(%r3)
	std %r4, 1056(%r3)
	ld %r4, 1192(%r3)
	std %r4, 1064(%r3)
	ld %r4, 1200(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1208(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1280(%r3)
	std %r4, 512(%r3)
	ld %r4, 1288(%r3)
	std %r4, 520(%r3)
	ld %r4, 1296(%r3)
	std %r4, 528(%r3)
	ld %r4, 1304(%r3)
	std %r4, 536(%r3)
	ld %r4, 1440(%r3)
	std %r4, 544(%r3)
	ld %r4, 1448(%r3)
	std %r4, 552(%r3)
	ld %r4, 1456(%r3)
	std %r4, 560(%r3)
	ld %r4, 1464(%r3)
	std %r4, 568(%r3)
	bl {vg_p224_mul}
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
	ld %r4, 224(%r3)
	std %r4, 992(%r3)
	ld %r4, 232(%r3)
	std %r4, 1000(%r3)
	ld %r4, 240(%r3)
	std %r4, 1008(%r3)
	ld %r4, 248(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
29:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4352(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 992(%r3)
	ld %r5, 1024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 1032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 1040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 1048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
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
