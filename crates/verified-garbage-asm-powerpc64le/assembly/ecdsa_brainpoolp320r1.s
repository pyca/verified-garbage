// The functions of `src/ecdsa_brainpoolp320r1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_verify:
	stdu %r1, -112(%r1)
	addi %r8, %r1, 32
	li %r11, 40
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
	addi %r10, %r8, 40
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
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1336(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1344(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1352(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1360(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1368(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1376(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1416(%r3)
	lis %r11, -3661
	ori %r11, %r11, 11815
	stw %r11, 64(%r3)
	lis %r11, -812
	ori %r11, %r11, 4785
	stw %r11, 68(%r3)
	lis %r11, 30867
	ori %r11, %r11, 60456
	stw %r11, 72(%r3)
	lis %r11, 20370
	ori %r11, %r11, 47596
	stw %r11, 76(%r3)
	lis %r11, -2316
	ori %r11, %r11, 3567
	stw %r11, 80(%r3)
	lis %r11, -1649
	ori %r11, %r11, 53158
	stw %r11, 84(%r3)
	lis %r11, -11775
	ori %r11, %r11, 57445
	stw %r11, 88(%r3)
	lis %r11, -7876
	ori %r11, %r11, 30814
	stw %r11, 92(%r3)
	lis %r11, 14012
	ori %r11, %r11, 20407
	stw %r11, 96(%r3)
	lis %r11, -11426
	ori %r11, %r11, 18208
	stw %r11, 100(%r3)
	lis %r11, 17605
	ori %r11, %r11, 37649
	stw %r11, 104(%r3)
	lis %r11, -31087
	ori %r11, %r11, 21851
	stw %r11, 108(%r3)
	lis %r11, -4474
	ori %r11, %r11, 22761
	stw %r11, 112(%r3)
	lis %r11, 11592
	ori %r11, %r11, 11975
	stw %r11, 116(%r3)
	lis %r11, -18801
	ori %r11, %r11, 4771
	stw %r11, 120(%r3)
	lis %r11, -1649
	ori %r11, %r11, 53157
	stw %r11, 124(%r3)
	lis %r11, -11775
	ori %r11, %r11, 57445
	stw %r11, 128(%r3)
	lis %r11, -7876
	ori %r11, %r11, 30814
	stw %r11, 132(%r3)
	lis %r11, 14012
	ori %r11, %r11, 20407
	stw %r11, 136(%r3)
	lis %r11, -11426
	ori %r11, %r11, 18208
	stw %r11, 140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 188(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 1
	stw %r11, 224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 0
	stw %r11, 256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 260(%r3)
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 264(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 268(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 272(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 276(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 280(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 284(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 288(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 292(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 296(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 300(%r3)
	lis %r11, 3953
	ori %r11, %r11, 13730
	stw %r11, 304(%r3)
	lis %r11, 8371
	ori %r11, %r11, 62075
	stw %r11, 308(%r3)
	lis %r11, -23614
	ori %r11, %r11, 57222
	stw %r11, 312(%r3)
	lis %r11, 1012
	ori %r11, %r11, 27245
	stw %r11, 316(%r3)
	lis %r11, -17512
	ori %r11, %r11, 45075
	stw %r11, 320(%r3)
	lis %r11, -24263
	ori %r11, %r11, 41953
	stw %r11, 324(%r3)
	lis %r11, -12821
	ori %r11, %r11, 14047
	stw %r11, 328(%r3)
	lis %r11, 14901
	ori %r11, %r11, 39144
	stw %r11, 332(%r3)
	lis %r11, -12606
	ori %r11, %r11, 40294
	stw %r11, 336(%r3)
	lis %r11, 18043
	ori %r11, %r11, 47289
	stw %r11, 340(%r3)
	lis %r11, 23663
	ori %r11, %r11, 13568
	stw %r11, 344(%r3)
	lis %r11, 25058
	ori %r11, %r11, 58758
	stw %r11, 348(%r3)
	lis %r11, 28773
	ori %r11, %r11, 39103
	stw %r11, 352(%r3)
	lis %r11, -24822
	ori %r11, %r11, 49089
	stw %r11, 356(%r3)
	lis %r11, -10960
	ori %r11, %r11, 37132
	stw %r11, 360(%r3)
	lis %r11, 21989
	ori %r11, %r11, 1601
	stw %r11, 364(%r3)
	lis %r11, -15405
	ori %r11, %r11, 16987
	stw %r11, 368(%r3)
	lis %r11, -3594
	ori %r11, %r11, 58520
	stw %r11, 372(%r3)
	lis %r11, 3872
	ori %r11, %r11, 23241
	stw %r11, 376(%r3)
	lis %r11, 4839
	ori %r11, %r11, 33054
	stw %r11, 380(%r3)
	lis %r11, 23932
	ori %r11, %r11, 2745
	stw %r11, 384(%r3)
	lis %r11, -17006
	ori %r11, %r11, 24176
	stw %r11, 388(%r3)
	lis %r11, -8500
	ori %r11, %r11, 61691
	stw %r11, 392(%r3)
	lis %r11, -4496
	ori %r11, %r11, 65188
	stw %r11, 396(%r3)
	lis %r11, 7421
	ori %r11, %r11, 37790
	stw %r11, 400(%r3)
	lis %r11, 28714
	ori %r11, %r11, 64560
	stw %r11, 404(%r3)
	lis %r11, -16558
	ori %r11, %r11, 8691
	stw %r11, 408(%r3)
	lis %r11, 22095
	ori %r11, %r11, 60931
	stw %r11, 412(%r3)
	lis %r11, 16819
	ori %r11, %r11, 62692
	stw %r11, 416(%r3)
	lis %r11, 17518
	ori %r11, %r11, 63667
	stw %r11, 420(%r3)
	lis %r11, 18380
	ori %r11, %r11, 24908
	stw %r11, 424(%r3)
	lis %r11, 21505
	ori %r11, %r11, 14215
	stw %r11, 428(%r3)
	lis %r11, -32738
	ori %r11, %r11, 57977
	stw %r11, 432(%r3)
	lis %r11, -14721
	ori %r11, %r11, 34311
	stw %r11, 436(%r3)
	lis %r11, -20673
	ori %r11, %r11, 3063
	stw %r11, 440(%r3)
	lis %r11, 21523
	ori %r11, %r11, 17238
	stw %r11, 444(%r3)
	lis %r11, -32283
	ori %r11, %r11, 48761
	stw %r11, 448(%r3)
	lis %r11, -1174
	ori %r11, %r11, 6689
	stw %r11, 452(%r3)
	lis %r11, -17036
	ori %r11, %r11, 43914
	stw %r11, 456(%r3)
	lis %r11, 30362
	ori %r11, %r11, 37762
	stw %r11, 460(%r3)
	lis %r11, 9491
	ori %r11, %r11, 58573
	stw %r11, 464(%r3)
	lis %r11, 26525
	ori %r11, %r11, 10719
	stw %r11, 468(%r3)
	lis %r11, -7967
	ori %r11, %r11, 26629
	stw %r11, 472(%r3)
	lis %r11, -28221
	ori %r11, %r11, 27
	stw %r11, 476(%r3)
	lis %r11, -20602
	ori %r11, %r11, 50185
	stw %r11, 480(%r3)
	lis %r11, -31053
	ori %r11, %r11, 12476
	stw %r11, 484(%r3)
	lis %r11, 20067
	ori %r11, %r11, 37118
	stw %r11, 488(%r3)
	lis %r11, -7411
	ori %r11, %r11, 13604
	stw %r11, 492(%r3)
	lis %r11, 12800
	ori %r11, %r11, 45391
	stw %r11, 496(%r3)
	lis %r11, 12780
	ori %r11, %r11, 34759
	stw %r11, 500(%r3)
	lis %r11, -17606
	ori %r11, %r11, 27887
	stw %r11, 504(%r3)
	lis %r11, 31086
	ori %r11, %r11, 43684
	stw %r11, 508(%r3)
	lis %r11, 4473
	ori %r11, %r11, 42774
	stw %r11, 512(%r3)
	lis %r11, -11593
	ori %r11, %r11, 53560
	stw %r11, 516(%r3)
	lis %r11, 18800
	ori %r11, %r11, 60764
	stw %r11, 520(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12378
	stw %r11, 524(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 528(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 532(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 536(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 540(%r3)
	lis %r11, -3661
	ori %r11, %r11, 11813
	stw %r11, 544(%r3)
	lis %r11, -812
	ori %r11, %r11, 4785
	stw %r11, 548(%r3)
	lis %r11, 30867
	ori %r11, %r11, 60456
	stw %r11, 552(%r3)
	lis %r11, 20370
	ori %r11, %r11, 47596
	stw %r11, 556(%r3)
	lis %r11, -2316
	ori %r11, %r11, 3567
	stw %r11, 560(%r3)
	lis %r11, -1649
	ori %r11, %r11, 53158
	stw %r11, 564(%r3)
	lis %r11, -11775
	ori %r11, %r11, 57445
	stw %r11, 568(%r3)
	lis %r11, -7876
	ori %r11, %r11, 30814
	stw %r11, 572(%r3)
	lis %r11, 14012
	ori %r11, %r11, 20407
	stw %r11, 576(%r3)
	lis %r11, -11426
	ori %r11, %r11, 18208
	stw %r11, 580(%r3)
	lis %r11, 17605
	ori %r11, %r11, 37647
	stw %r11, 584(%r3)
	lis %r11, -31087
	ori %r11, %r11, 21851
	stw %r11, 588(%r3)
	lis %r11, -4474
	ori %r11, %r11, 22761
	stw %r11, 592(%r3)
	lis %r11, 11592
	ori %r11, %r11, 11975
	stw %r11, 596(%r3)
	lis %r11, -18801
	ori %r11, %r11, 4771
	stw %r11, 600(%r3)
	lis %r11, -1649
	ori %r11, %r11, 53157
	stw %r11, 604(%r3)
	lis %r11, -11775
	ori %r11, %r11, 57445
	stw %r11, 608(%r3)
	lis %r11, -7876
	ori %r11, %r11, 30814
	stw %r11, 612(%r3)
	lis %r11, 14012
	ori %r11, %r11, 20407
	stw %r11, 616(%r3)
	lis %r11, -11426
	ori %r11, %r11, 18208
	stw %r11, 620(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 624(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 628(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 632(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 636(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 640(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 644(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 648(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 652(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 656(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 660(%r3)
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 664(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 668(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 672(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 676(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 680(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 684(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 688(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 692(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 696(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 700(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 708(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 712(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 716(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 720(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 724(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 728(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 732(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 736(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 740(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1824(%r3)
	or %r12, %r5, %r5
	li %r31, 40
25:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1304(%r4)
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
	li %r31, 40
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 544(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4416(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4417(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4418(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4419(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4420(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4421(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4422(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4423(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r31, 40
27:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 584(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4736(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4737(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4738(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4739(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4740(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4741(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4742(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4743(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	addi %r6, %r12, 40
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1264(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1272(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1280(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1288(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1296(%r3)
	lis %r11, 29755
	ori %r11, %r11, 21241
	stw %r11, 1624(%r3)
	lis %r11, -26290
	ori %r11, %r11, 59530
	stw %r11, 1628(%r3)
	lis %r11, -28567
	ori %r11, %r11, 30959
	stw %r11, 1632(%r3)
	lis %r11, -15801
	ori %r11, %r11, 35469
	stw %r11, 1636(%r3)
	lis %r11, 12485
	ori %r11, %r11, 46710
	stw %r11, 1640(%r3)
	lis %r11, 8012
	ori %r11, %r11, 34847
	stw %r11, 1644(%r3)
	lis %r11, -6636
	ori %r11, %r11, 54994
	stw %r11, 1648(%r3)
	lis %r11, 21589
	ori %r11, %r11, 43364
	stw %r11, 1652(%r3)
	lis %r11, 27693
	ori %r11, %r11, 37458
	stw %r11, 1656(%r3)
	lis %r11, -23975
	ori %r11, %r11, 47690
	stw %r11, 1660(%r3)
	lis %r11, -16399
	ori %r11, %r11, 56090
	stw %r11, 1664(%r3)
	lis %r11, -14034
	ori %r11, %r11, 22776
	stw %r11, 1668(%r3)
	lis %r11, 8324
	ori %r11, %r11, 31493
	stw %r11, 1672(%r3)
	lis %r11, 5306
	ori %r11, %r11, 48094
	stw %r11, 1676(%r3)
	lis %r11, -27043
	ori %r11, %r11, 36601
	stw %r11, 1680(%r3)
	lis %r11, 6230
	ori %r11, %r11, 57818
	stw %r11, 1684(%r3)
	lis %r11, 8861
	ori %r11, %r11, 269
	stw %r11, 1688(%r3)
	lis %r11, -28294
	ori %r11, %r11, 40050
	stw %r11, 1692(%r3)
	lis %r11, 10632
	ori %r11, %r11, 21352
	stw %r11, 1696(%r3)
	lis %r11, -27850
	ori %r11, %r11, 45002
	stw %r11, 1700(%r3)
	addi %r6, %r14, 1
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1416(%r3)
	addi %r6, %r6, 40
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1504(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1512(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1520(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1528(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1536(%r3)
	lbz %r4, 0(%r14)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1384(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1388(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1392(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1396(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1400(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1404(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1408(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1412(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1416(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1420(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1504(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1508(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1512(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1516(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1520(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1524(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1528(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1532(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1536(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1540(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r4, 1424
	li %r5, 1384
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1464
	li %r5, 1504
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1544
	li %r5, 1464
	li %r6, 1464
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1704
	li %r5, 1424
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1704
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1704
	li %r5, 304
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1584
	li %r5, 1744
	li %r6, 1704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1744
	li %r5, 1584
	li %r6, 1664
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1704
	li %r5, 1544
	li %r6, 1744
	bl {vg_brainpoolp320r1_sub_mod_p}
	ld %r5, 1704(%r3)
	ld %r4, 1712(%r3)
	or %r5, %r5, %r4
	ld %r4, 1720(%r3)
	or %r5, %r5, %r4
	ld %r4, 1728(%r3)
	or %r5, %r5, %r4
	ld %r4, 1736(%r3)
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
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r10, 1824(%r3)
	ld %r4, 384(%r3)
	ld %r5, 1424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 392(%r3)
	ld %r5, 1432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 400(%r3)
	ld %r5, 1440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 408(%r3)
	ld %r5, 1448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 416(%r3)
	ld %r5, 1456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 424(%r3)
	ld %r5, 1464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1784(%r3)
	ld %r4, 432(%r3)
	ld %r5, 1472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1792(%r3)
	ld %r4, 440(%r3)
	ld %r5, 1480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1800(%r3)
	ld %r4, 448(%r3)
	ld %r5, 1488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1808(%r3)
	ld %r4, 456(%r3)
	ld %r5, 1496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1816(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1304(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1308(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1312(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1316(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1320(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1324(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1328(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1332(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1336(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1340(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1304(%r3)
	ld %r4, 1312(%r3)
	or %r5, %r5, %r4
	ld %r4, 1320(%r3)
	or %r5, %r5, %r4
	ld %r4, 1328(%r3)
	or %r5, %r5, %r4
	ld %r4, 1336(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1264(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1268(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1272(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1276(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1280(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1284(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1288(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1292(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1296(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1300(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1264(%r3)
	ld %r4, 1272(%r3)
	or %r5, %r5, %r4
	ld %r4, 1280(%r3)
	or %r5, %r5, %r4
	ld %r4, 1288(%r3)
	or %r5, %r5, %r4
	ld %r4, 1296(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r4, 1544
	li %r5, 1264
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r4, 1544(%r3)
	std %r4, 744(%r3)
	ld %r4, 1552(%r3)
	std %r4, 752(%r3)
	ld %r4, 1560(%r3)
	std %r4, 760(%r3)
	ld %r4, 1568(%r3)
	std %r4, 768(%r3)
	ld %r4, 1576(%r3)
	std %r4, 776(%r3)
	li %r4, 1064
	li %r5, 1544
	li %r6, 1544
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 784
	li %r5, 744
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 824
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 864
	li %r5, 824
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 904
	li %r5, 864
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 944
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 984
	li %r5, 944
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1024
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r4, 984(%r3)
	std %r4, 1224(%r3)
	ld %r4, 992(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1000(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1008(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1016(%r3)
	std %r4, 1256(%r3)
	li %r31, 6
28:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
29:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
210:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
211:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
212:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 11
213:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
214:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
215:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
216:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
218:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
220:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
221:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
222:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
223:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
224:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
226:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
227:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 12
228:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
229:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
230:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
231:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
233:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 2
234:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
235:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
236:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
237:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
238:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
239:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
240:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
241:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
242:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
243:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
244:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
245:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
246:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 9
247:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
248:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
249:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
250:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
251:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
252:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
253:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
254:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
255:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
256:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
257:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
258:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
259:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
260:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
261:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
262:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
263:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
264:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
265:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
266:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
267:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
268:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
269:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1664
	li %r5, 1344
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1624
	li %r5, 1304
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1704
	li %r5, 1664
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1744
	li %r5, 1624
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1424
	li %r5, 1704
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1464
	li %r5, 1744
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 40
270:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1424(%r4)
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
	bne %cr0, 270b
	lis %r11, -16399
	ori %r11, %r11, 56090
	stw %r11, 1664(%r3)
	lis %r11, -14034
	ori %r11, %r11, 22776
	stw %r11, 1668(%r3)
	lis %r11, 8324
	ori %r11, %r11, 31493
	stw %r11, 1672(%r3)
	lis %r11, 5306
	ori %r11, %r11, 48094
	stw %r11, 1676(%r3)
	lis %r11, -27043
	ori %r11, %r11, 36601
	stw %r11, 1680(%r3)
	lis %r11, 6230
	ori %r11, %r11, 57818
	stw %r11, 1684(%r3)
	lis %r11, 8861
	ori %r11, %r11, 269
	stw %r11, 1688(%r3)
	lis %r11, -28294
	ori %r11, %r11, 40050
	stw %r11, 1692(%r3)
	lis %r11, 10632
	ori %r11, %r11, 21352
	stw %r11, 1696(%r3)
	lis %r11, -27850
	ori %r11, %r11, 45002
	stw %r11, 1700(%r3)
	ld %r4, 384(%r3)
	std %r4, 3272(%r3)
	ld %r4, 392(%r3)
	std %r4, 3280(%r3)
	ld %r4, 400(%r3)
	std %r4, 3288(%r3)
	ld %r4, 408(%r3)
	std %r4, 3296(%r3)
	ld %r4, 416(%r3)
	std %r4, 3304(%r3)
	ld %r4, 424(%r3)
	std %r4, 3312(%r3)
	ld %r4, 432(%r3)
	std %r4, 3320(%r3)
	ld %r4, 440(%r3)
	std %r4, 3328(%r3)
	ld %r4, 448(%r3)
	std %r4, 3336(%r3)
	ld %r4, 456(%r3)
	std %r4, 3344(%r3)
	ld %r4, 264(%r3)
	std %r4, 3352(%r3)
	ld %r4, 272(%r3)
	std %r4, 3360(%r3)
	ld %r4, 280(%r3)
	std %r4, 3368(%r3)
	ld %r4, 288(%r3)
	std %r4, 3376(%r3)
	ld %r4, 296(%r3)
	std %r4, 3384(%r3)
	ld %r4, 304(%r3)
	std %r4, 3392(%r3)
	ld %r4, 312(%r3)
	std %r4, 3400(%r3)
	ld %r4, 320(%r3)
	std %r4, 3408(%r3)
	ld %r4, 328(%r3)
	std %r4, 3416(%r3)
	ld %r4, 336(%r3)
	std %r4, 3424(%r3)
	ld %r4, 344(%r3)
	std %r4, 3432(%r3)
	ld %r4, 352(%r3)
	std %r4, 3440(%r3)
	ld %r4, 360(%r3)
	std %r4, 3448(%r3)
	ld %r4, 368(%r3)
	std %r4, 3456(%r3)
	ld %r4, 376(%r3)
	std %r4, 3464(%r3)
	lis %r11, 2198
	ori %r11, %r11, 21888
	stw %r11, 624(%r3)
	lis %r11, 19873
	ori %r11, %r11, 41135
	stw %r11, 628(%r3)
	lis %r11, 25931
	ori %r11, %r11, 28825
	stw %r11, 632(%r3)
	lis %r11, 25670
	ori %r11, %r11, 63964
	stw %r11, 636(%r3)
	lis %r11, 29184
	ori %r11, %r11, 28887
	stw %r11, 640(%r3)
	lis %r11, -20072
	ori %r11, %r11, 37574
	stw %r11, 644(%r3)
	lis %r11, -13122
	ori %r11, %r11, 17146
	stw %r11, 648(%r3)
	lis %r11, -8207
	ori %r11, %r11, 43243
	stw %r11, 652(%r3)
	lis %r11, -27152
	ori %r11, %r11, 7190
	stw %r11, 656(%r3)
	lis %r11, 17621
	ori %r11, %r11, 41073
	stw %r11, 660(%r3)
	lis %r11, -2775
	ori %r11, %r11, 20243
	stw %r11, 664(%r3)
	lis %r11, 15453
	ori %r11, %r11, 28964
	stw %r11, 668(%r3)
	lis %r11, 31571
	ori %r11, %r11, 31306
	stw %r11, 672(%r3)
	lis %r11, 13894
	ori %r11, %r11, 45918
	stw %r11, 676(%r3)
	lis %r11, -9190
	ori %r11, %r11, 17111
	stw %r11, 680(%r3)
	lis %r11, -29556
	ori %r11, %r11, 35437
	stw %r11, 684(%r3)
	lis %r11, 2155
	ori %r11, %r11, 55457
	stw %r11, 688(%r3)
	lis %r11, -29600
	ori %r11, %r11, 44970
	stw %r11, 692(%r3)
	lis %r11, 31933
	ori %r11, %r11, 23878
	stw %r11, 696(%r3)
	lis %r11, -19149
	ori %r11, %r11, 48074
	stw %r11, 700(%r3)
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 704(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 708(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 712(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 716(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 720(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 724(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 728(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 732(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 736(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 740(%r3)
	li %r31, 46
271:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -45
	cmpldi %cr0, %r6, 0
	beq %cr0, 272f
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
	b 273f
272:
	li %r9, 0
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
273:
	addi %r9, %r9, -64
	rldicl %r4, %r9, 1, 63
	li %r5, 0
	subf %r4, %r4, %r5
	xor %r9, %r9, %r4
	subf %r9, %r4, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_BRAINPOOLP320R1_COMB}
	addi %r8, %r8, ({VG_BRAINPOOLP320R1_COMB}
	li %r4, 5120
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	li %r7, 1
274:
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 274b
	li %r4, 3272
	stxvd2x 32, %r3, %r4
	li %r4, 3288
	stxvd2x 33, %r3, %r4
	li %r4, 3304
	stxvd2x 34, %r3, %r4
	li %r4, 3320
	stxvd2x 35, %r3, %r4
	li %r4, 3336
	stxvd2x 36, %r3, %r4
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 3352(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 3356(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 3360(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 3364(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 3368(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 3372(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 3376(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 3380(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 3384(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 3388(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3312(%r3)
	ld %r5, 3352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3312(%r3)
	ld %r4, 3320(%r3)
	ld %r5, 3360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3320(%r3)
	ld %r4, 3328(%r3)
	ld %r5, 3368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3328(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 3376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3336(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 3384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3344(%r3)
	ld %r4, 3352(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3352(%r3)
	ld %r4, 3360(%r3)
	ld %r5, 192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3360(%r3)
	ld %r4, 3368(%r3)
	ld %r5, 200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3368(%r3)
	ld %r4, 3376(%r3)
	ld %r5, 208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3376(%r3)
	ld %r4, 3384(%r3)
	ld %r5, 216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3384(%r3)
	li %r4, 864
	li %r5, 184
	li %r6, 3312
	bl {vg_brainpoolp320r1_sub_mod_p}
	addi %r6, %r31, -45
	cmpldi %cr0, %r6, 0
	beq %cr0, 275f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	addi %r10, %r4, -1
	b 276f
275:
	li %r10, 0
	addi %r10, %r10, -1
276:
	ld %r4, 3312(%r3)
	ld %r5, 864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3312(%r3)
	ld %r4, 3320(%r3)
	ld %r5, 872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3320(%r3)
	ld %r4, 3328(%r3)
	ld %r5, 880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3328(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3336(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3344(%r3)
	ld %r4, 624(%r3)
	std %r4, 3152(%r3)
	ld %r4, 632(%r3)
	std %r4, 3160(%r3)
	ld %r4, 640(%r3)
	std %r4, 3168(%r3)
	ld %r4, 648(%r3)
	std %r4, 3176(%r3)
	ld %r4, 656(%r3)
	std %r4, 3184(%r3)
	ld %r4, 664(%r3)
	std %r4, 3192(%r3)
	ld %r4, 672(%r3)
	std %r4, 3200(%r3)
	ld %r4, 680(%r3)
	std %r4, 3208(%r3)
	ld %r4, 688(%r3)
	std %r4, 3216(%r3)
	ld %r4, 696(%r3)
	std %r4, 3224(%r3)
	ld %r4, 704(%r3)
	std %r4, 3232(%r3)
	ld %r4, 712(%r3)
	std %r4, 3240(%r3)
	ld %r4, 720(%r3)
	std %r4, 3248(%r3)
	ld %r4, 728(%r3)
	std %r4, 3256(%r3)
	ld %r4, 736(%r3)
	std %r4, 3264(%r3)
	bl {vg_brainpoolp320r1_point_add}
	ld %r4, 3032(%r3)
	std %r4, 624(%r3)
	ld %r4, 3040(%r3)
	std %r4, 632(%r3)
	ld %r4, 3048(%r3)
	std %r4, 640(%r3)
	ld %r4, 3056(%r3)
	std %r4, 648(%r3)
	ld %r4, 3064(%r3)
	std %r4, 656(%r3)
	ld %r4, 3072(%r3)
	std %r4, 664(%r3)
	ld %r4, 3080(%r3)
	std %r4, 672(%r3)
	ld %r4, 3088(%r3)
	std %r4, 680(%r3)
	ld %r4, 3096(%r3)
	std %r4, 688(%r3)
	ld %r4, 3104(%r3)
	std %r4, 696(%r3)
	ld %r4, 3112(%r3)
	std %r4, 704(%r3)
	ld %r4, 3120(%r3)
	std %r4, 712(%r3)
	ld %r4, 3128(%r3)
	std %r4, 720(%r3)
	ld %r4, 3136(%r3)
	std %r4, 728(%r3)
	ld %r4, 3144(%r3)
	std %r4, 736(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	ld %r4, 624(%r3)
	std %r4, 1704(%r3)
	ld %r4, 632(%r3)
	std %r4, 1712(%r3)
	ld %r4, 640(%r3)
	std %r4, 1720(%r3)
	ld %r4, 648(%r3)
	std %r4, 1728(%r3)
	ld %r4, 656(%r3)
	std %r4, 1736(%r3)
	ld %r4, 664(%r3)
	std %r4, 1744(%r3)
	ld %r4, 672(%r3)
	std %r4, 1752(%r3)
	ld %r4, 680(%r3)
	std %r4, 1760(%r3)
	ld %r4, 688(%r3)
	std %r4, 1768(%r3)
	ld %r4, 696(%r3)
	std %r4, 1776(%r3)
	ld %r4, 704(%r3)
	std %r4, 1544(%r3)
	ld %r4, 712(%r3)
	std %r4, 1552(%r3)
	ld %r4, 720(%r3)
	std %r4, 1560(%r3)
	ld %r4, 728(%r3)
	std %r4, 1568(%r3)
	ld %r4, 736(%r3)
	std %r4, 1576(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 624(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 628(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 632(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 636(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 640(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 644(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 648(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 652(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 656(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 660(%r3)
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 664(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 668(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 672(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 676(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 680(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 684(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 688(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 692(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 696(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 700(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 708(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 712(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 716(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 720(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 724(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 728(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 732(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 736(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 740(%r3)
	li %r31, 40
277:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1464(%r4)
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
	bne %cr0, 277b
	ld %r4, 184(%r3)
	std %r4, 5056(%r3)
	ld %r4, 192(%r3)
	std %r4, 5064(%r3)
	ld %r4, 200(%r3)
	std %r4, 5072(%r3)
	ld %r4, 208(%r3)
	std %r4, 5080(%r3)
	ld %r4, 216(%r3)
	std %r4, 5088(%r3)
	ld %r4, 264(%r3)
	std %r4, 5096(%r3)
	ld %r4, 272(%r3)
	std %r4, 5104(%r3)
	ld %r4, 280(%r3)
	std %r4, 5112(%r3)
	ld %r4, 288(%r3)
	std %r4, 5120(%r3)
	ld %r4, 296(%r3)
	std %r4, 5128(%r3)
	ld %r4, 184(%r3)
	std %r4, 5136(%r3)
	ld %r4, 192(%r3)
	std %r4, 5144(%r3)
	ld %r4, 200(%r3)
	std %r4, 5152(%r3)
	ld %r4, 208(%r3)
	std %r4, 5160(%r3)
	ld %r4, 216(%r3)
	std %r4, 5168(%r3)
	ld %r4, 1584(%r3)
	std %r4, 5176(%r3)
	ld %r4, 1592(%r3)
	std %r4, 5184(%r3)
	ld %r4, 1600(%r3)
	std %r4, 5192(%r3)
	ld %r4, 1608(%r3)
	std %r4, 5200(%r3)
	ld %r4, 1616(%r3)
	std %r4, 5208(%r3)
	ld %r4, 1784(%r3)
	std %r4, 5216(%r3)
	ld %r4, 1792(%r3)
	std %r4, 5224(%r3)
	ld %r4, 1800(%r3)
	std %r4, 5232(%r3)
	ld %r4, 1808(%r3)
	std %r4, 5240(%r3)
	ld %r4, 1816(%r3)
	std %r4, 5248(%r3)
	ld %r4, 264(%r3)
	std %r4, 5256(%r3)
	ld %r4, 272(%r3)
	std %r4, 5264(%r3)
	ld %r4, 280(%r3)
	std %r4, 5272(%r3)
	ld %r4, 288(%r3)
	std %r4, 5280(%r3)
	ld %r4, 296(%r3)
	std %r4, 5288(%r3)
	ld %r4, 1584(%r3)
	std %r4, 744(%r3)
	ld %r4, 1592(%r3)
	std %r4, 752(%r3)
	ld %r4, 1600(%r3)
	std %r4, 760(%r3)
	ld %r4, 1608(%r3)
	std %r4, 768(%r3)
	ld %r4, 1616(%r3)
	std %r4, 776(%r3)
	ld %r4, 1784(%r3)
	std %r4, 784(%r3)
	ld %r4, 1792(%r3)
	std %r4, 792(%r3)
	ld %r4, 1800(%r3)
	std %r4, 800(%r3)
	ld %r4, 1808(%r3)
	std %r4, 808(%r3)
	ld %r4, 1816(%r3)
	std %r4, 816(%r3)
	ld %r4, 264(%r3)
	std %r4, 824(%r3)
	ld %r4, 272(%r3)
	std %r4, 832(%r3)
	ld %r4, 280(%r3)
	std %r4, 840(%r3)
	ld %r4, 288(%r3)
	std %r4, 848(%r3)
	ld %r4, 296(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5296(%r3)
	ld %r4, 872(%r3)
	std %r4, 5304(%r3)
	ld %r4, 880(%r3)
	std %r4, 5312(%r3)
	ld %r4, 888(%r3)
	std %r4, 5320(%r3)
	ld %r4, 896(%r3)
	std %r4, 5328(%r3)
	ld %r4, 904(%r3)
	std %r4, 5336(%r3)
	ld %r4, 912(%r3)
	std %r4, 5344(%r3)
	ld %r4, 920(%r3)
	std %r4, 5352(%r3)
	ld %r4, 928(%r3)
	std %r4, 5360(%r3)
	ld %r4, 936(%r3)
	std %r4, 5368(%r3)
	ld %r4, 944(%r3)
	std %r4, 5376(%r3)
	ld %r4, 952(%r3)
	std %r4, 5384(%r3)
	ld %r4, 960(%r3)
	std %r4, 5392(%r3)
	ld %r4, 968(%r3)
	std %r4, 5400(%r3)
	ld %r4, 976(%r3)
	std %r4, 5408(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5416(%r3)
	ld %r4, 872(%r3)
	std %r4, 5424(%r3)
	ld %r4, 880(%r3)
	std %r4, 5432(%r3)
	ld %r4, 888(%r3)
	std %r4, 5440(%r3)
	ld %r4, 896(%r3)
	std %r4, 5448(%r3)
	ld %r4, 904(%r3)
	std %r4, 5456(%r3)
	ld %r4, 912(%r3)
	std %r4, 5464(%r3)
	ld %r4, 920(%r3)
	std %r4, 5472(%r3)
	ld %r4, 928(%r3)
	std %r4, 5480(%r3)
	ld %r4, 936(%r3)
	std %r4, 5488(%r3)
	ld %r4, 944(%r3)
	std %r4, 5496(%r3)
	ld %r4, 952(%r3)
	std %r4, 5504(%r3)
	ld %r4, 960(%r3)
	std %r4, 5512(%r3)
	ld %r4, 968(%r3)
	std %r4, 5520(%r3)
	ld %r4, 976(%r3)
	std %r4, 5528(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5536(%r3)
	ld %r4, 872(%r3)
	std %r4, 5544(%r3)
	ld %r4, 880(%r3)
	std %r4, 5552(%r3)
	ld %r4, 888(%r3)
	std %r4, 5560(%r3)
	ld %r4, 896(%r3)
	std %r4, 5568(%r3)
	ld %r4, 904(%r3)
	std %r4, 5576(%r3)
	ld %r4, 912(%r3)
	std %r4, 5584(%r3)
	ld %r4, 920(%r3)
	std %r4, 5592(%r3)
	ld %r4, 928(%r3)
	std %r4, 5600(%r3)
	ld %r4, 936(%r3)
	std %r4, 5608(%r3)
	ld %r4, 944(%r3)
	std %r4, 5616(%r3)
	ld %r4, 952(%r3)
	std %r4, 5624(%r3)
	ld %r4, 960(%r3)
	std %r4, 5632(%r3)
	ld %r4, 968(%r3)
	std %r4, 5640(%r3)
	ld %r4, 976(%r3)
	std %r4, 5648(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5656(%r3)
	ld %r4, 872(%r3)
	std %r4, 5664(%r3)
	ld %r4, 880(%r3)
	std %r4, 5672(%r3)
	ld %r4, 888(%r3)
	std %r4, 5680(%r3)
	ld %r4, 896(%r3)
	std %r4, 5688(%r3)
	ld %r4, 904(%r3)
	std %r4, 5696(%r3)
	ld %r4, 912(%r3)
	std %r4, 5704(%r3)
	ld %r4, 920(%r3)
	std %r4, 5712(%r3)
	ld %r4, 928(%r3)
	std %r4, 5720(%r3)
	ld %r4, 936(%r3)
	std %r4, 5728(%r3)
	ld %r4, 944(%r3)
	std %r4, 5736(%r3)
	ld %r4, 952(%r3)
	std %r4, 5744(%r3)
	ld %r4, 960(%r3)
	std %r4, 5752(%r3)
	ld %r4, 968(%r3)
	std %r4, 5760(%r3)
	ld %r4, 976(%r3)
	std %r4, 5768(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5776(%r3)
	ld %r4, 872(%r3)
	std %r4, 5784(%r3)
	ld %r4, 880(%r3)
	std %r4, 5792(%r3)
	ld %r4, 888(%r3)
	std %r4, 5800(%r3)
	ld %r4, 896(%r3)
	std %r4, 5808(%r3)
	ld %r4, 904(%r3)
	std %r4, 5816(%r3)
	ld %r4, 912(%r3)
	std %r4, 5824(%r3)
	ld %r4, 920(%r3)
	std %r4, 5832(%r3)
	ld %r4, 928(%r3)
	std %r4, 5840(%r3)
	ld %r4, 936(%r3)
	std %r4, 5848(%r3)
	ld %r4, 944(%r3)
	std %r4, 5856(%r3)
	ld %r4, 952(%r3)
	std %r4, 5864(%r3)
	ld %r4, 960(%r3)
	std %r4, 5872(%r3)
	ld %r4, 968(%r3)
	std %r4, 5880(%r3)
	ld %r4, 976(%r3)
	std %r4, 5888(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 5896(%r3)
	ld %r4, 872(%r3)
	std %r4, 5904(%r3)
	ld %r4, 880(%r3)
	std %r4, 5912(%r3)
	ld %r4, 888(%r3)
	std %r4, 5920(%r3)
	ld %r4, 896(%r3)
	std %r4, 5928(%r3)
	ld %r4, 904(%r3)
	std %r4, 5936(%r3)
	ld %r4, 912(%r3)
	std %r4, 5944(%r3)
	ld %r4, 920(%r3)
	std %r4, 5952(%r3)
	ld %r4, 928(%r3)
	std %r4, 5960(%r3)
	ld %r4, 936(%r3)
	std %r4, 5968(%r3)
	ld %r4, 944(%r3)
	std %r4, 5976(%r3)
	ld %r4, 952(%r3)
	std %r4, 5984(%r3)
	ld %r4, 960(%r3)
	std %r4, 5992(%r3)
	ld %r4, 968(%r3)
	std %r4, 6000(%r3)
	ld %r4, 976(%r3)
	std %r4, 6008(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6016(%r3)
	ld %r4, 872(%r3)
	std %r4, 6024(%r3)
	ld %r4, 880(%r3)
	std %r4, 6032(%r3)
	ld %r4, 888(%r3)
	std %r4, 6040(%r3)
	ld %r4, 896(%r3)
	std %r4, 6048(%r3)
	ld %r4, 904(%r3)
	std %r4, 6056(%r3)
	ld %r4, 912(%r3)
	std %r4, 6064(%r3)
	ld %r4, 920(%r3)
	std %r4, 6072(%r3)
	ld %r4, 928(%r3)
	std %r4, 6080(%r3)
	ld %r4, 936(%r3)
	std %r4, 6088(%r3)
	ld %r4, 944(%r3)
	std %r4, 6096(%r3)
	ld %r4, 952(%r3)
	std %r4, 6104(%r3)
	ld %r4, 960(%r3)
	std %r4, 6112(%r3)
	ld %r4, 968(%r3)
	std %r4, 6120(%r3)
	ld %r4, 976(%r3)
	std %r4, 6128(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6136(%r3)
	ld %r4, 872(%r3)
	std %r4, 6144(%r3)
	ld %r4, 880(%r3)
	std %r4, 6152(%r3)
	ld %r4, 888(%r3)
	std %r4, 6160(%r3)
	ld %r4, 896(%r3)
	std %r4, 6168(%r3)
	ld %r4, 904(%r3)
	std %r4, 6176(%r3)
	ld %r4, 912(%r3)
	std %r4, 6184(%r3)
	ld %r4, 920(%r3)
	std %r4, 6192(%r3)
	ld %r4, 928(%r3)
	std %r4, 6200(%r3)
	ld %r4, 936(%r3)
	std %r4, 6208(%r3)
	ld %r4, 944(%r3)
	std %r4, 6216(%r3)
	ld %r4, 952(%r3)
	std %r4, 6224(%r3)
	ld %r4, 960(%r3)
	std %r4, 6232(%r3)
	ld %r4, 968(%r3)
	std %r4, 6240(%r3)
	ld %r4, 976(%r3)
	std %r4, 6248(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6256(%r3)
	ld %r4, 872(%r3)
	std %r4, 6264(%r3)
	ld %r4, 880(%r3)
	std %r4, 6272(%r3)
	ld %r4, 888(%r3)
	std %r4, 6280(%r3)
	ld %r4, 896(%r3)
	std %r4, 6288(%r3)
	ld %r4, 904(%r3)
	std %r4, 6296(%r3)
	ld %r4, 912(%r3)
	std %r4, 6304(%r3)
	ld %r4, 920(%r3)
	std %r4, 6312(%r3)
	ld %r4, 928(%r3)
	std %r4, 6320(%r3)
	ld %r4, 936(%r3)
	std %r4, 6328(%r3)
	ld %r4, 944(%r3)
	std %r4, 6336(%r3)
	ld %r4, 952(%r3)
	std %r4, 6344(%r3)
	ld %r4, 960(%r3)
	std %r4, 6352(%r3)
	ld %r4, 968(%r3)
	std %r4, 6360(%r3)
	ld %r4, 976(%r3)
	std %r4, 6368(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6376(%r3)
	ld %r4, 872(%r3)
	std %r4, 6384(%r3)
	ld %r4, 880(%r3)
	std %r4, 6392(%r3)
	ld %r4, 888(%r3)
	std %r4, 6400(%r3)
	ld %r4, 896(%r3)
	std %r4, 6408(%r3)
	ld %r4, 904(%r3)
	std %r4, 6416(%r3)
	ld %r4, 912(%r3)
	std %r4, 6424(%r3)
	ld %r4, 920(%r3)
	std %r4, 6432(%r3)
	ld %r4, 928(%r3)
	std %r4, 6440(%r3)
	ld %r4, 936(%r3)
	std %r4, 6448(%r3)
	ld %r4, 944(%r3)
	std %r4, 6456(%r3)
	ld %r4, 952(%r3)
	std %r4, 6464(%r3)
	ld %r4, 960(%r3)
	std %r4, 6472(%r3)
	ld %r4, 968(%r3)
	std %r4, 6480(%r3)
	ld %r4, 976(%r3)
	std %r4, 6488(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6496(%r3)
	ld %r4, 872(%r3)
	std %r4, 6504(%r3)
	ld %r4, 880(%r3)
	std %r4, 6512(%r3)
	ld %r4, 888(%r3)
	std %r4, 6520(%r3)
	ld %r4, 896(%r3)
	std %r4, 6528(%r3)
	ld %r4, 904(%r3)
	std %r4, 6536(%r3)
	ld %r4, 912(%r3)
	std %r4, 6544(%r3)
	ld %r4, 920(%r3)
	std %r4, 6552(%r3)
	ld %r4, 928(%r3)
	std %r4, 6560(%r3)
	ld %r4, 936(%r3)
	std %r4, 6568(%r3)
	ld %r4, 944(%r3)
	std %r4, 6576(%r3)
	ld %r4, 952(%r3)
	std %r4, 6584(%r3)
	ld %r4, 960(%r3)
	std %r4, 6592(%r3)
	ld %r4, 968(%r3)
	std %r4, 6600(%r3)
	ld %r4, 976(%r3)
	std %r4, 6608(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6616(%r3)
	ld %r4, 872(%r3)
	std %r4, 6624(%r3)
	ld %r4, 880(%r3)
	std %r4, 6632(%r3)
	ld %r4, 888(%r3)
	std %r4, 6640(%r3)
	ld %r4, 896(%r3)
	std %r4, 6648(%r3)
	ld %r4, 904(%r3)
	std %r4, 6656(%r3)
	ld %r4, 912(%r3)
	std %r4, 6664(%r3)
	ld %r4, 920(%r3)
	std %r4, 6672(%r3)
	ld %r4, 928(%r3)
	std %r4, 6680(%r3)
	ld %r4, 936(%r3)
	std %r4, 6688(%r3)
	ld %r4, 944(%r3)
	std %r4, 6696(%r3)
	ld %r4, 952(%r3)
	std %r4, 6704(%r3)
	ld %r4, 960(%r3)
	std %r4, 6712(%r3)
	ld %r4, 968(%r3)
	std %r4, 6720(%r3)
	ld %r4, 976(%r3)
	std %r4, 6728(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6736(%r3)
	ld %r4, 872(%r3)
	std %r4, 6744(%r3)
	ld %r4, 880(%r3)
	std %r4, 6752(%r3)
	ld %r4, 888(%r3)
	std %r4, 6760(%r3)
	ld %r4, 896(%r3)
	std %r4, 6768(%r3)
	ld %r4, 904(%r3)
	std %r4, 6776(%r3)
	ld %r4, 912(%r3)
	std %r4, 6784(%r3)
	ld %r4, 920(%r3)
	std %r4, 6792(%r3)
	ld %r4, 928(%r3)
	std %r4, 6800(%r3)
	ld %r4, 936(%r3)
	std %r4, 6808(%r3)
	ld %r4, 944(%r3)
	std %r4, 6816(%r3)
	ld %r4, 952(%r3)
	std %r4, 6824(%r3)
	ld %r4, 960(%r3)
	std %r4, 6832(%r3)
	ld %r4, 968(%r3)
	std %r4, 6840(%r3)
	ld %r4, 976(%r3)
	std %r4, 6848(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 744
	li %r6, 1584
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 1784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 824
	li %r6, 264
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1584
	li %r6, 1784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1584
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1784
	li %r6, 264
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 6856(%r3)
	ld %r4, 872(%r3)
	std %r4, 6864(%r3)
	ld %r4, 880(%r3)
	std %r4, 6872(%r3)
	ld %r4, 888(%r3)
	std %r4, 6880(%r3)
	ld %r4, 896(%r3)
	std %r4, 6888(%r3)
	ld %r4, 904(%r3)
	std %r4, 6896(%r3)
	ld %r4, 912(%r3)
	std %r4, 6904(%r3)
	ld %r4, 920(%r3)
	std %r4, 6912(%r3)
	ld %r4, 928(%r3)
	std %r4, 6920(%r3)
	ld %r4, 936(%r3)
	std %r4, 6928(%r3)
	ld %r4, 944(%r3)
	std %r4, 6936(%r3)
	ld %r4, 952(%r3)
	std %r4, 6944(%r3)
	ld %r4, 960(%r3)
	std %r4, 6952(%r3)
	ld %r4, 968(%r3)
	std %r4, 6960(%r3)
	ld %r4, 976(%r3)
	std %r4, 6968(%r3)
	ld %r4, 864(%r3)
	std %r4, 744(%r3)
	ld %r4, 872(%r3)
	std %r4, 752(%r3)
	ld %r4, 880(%r3)
	std %r4, 760(%r3)
	ld %r4, 888(%r3)
	std %r4, 768(%r3)
	ld %r4, 896(%r3)
	std %r4, 776(%r3)
	ld %r4, 904(%r3)
	std %r4, 784(%r3)
	ld %r4, 912(%r3)
	std %r4, 792(%r3)
	ld %r4, 920(%r3)
	std %r4, 800(%r3)
	ld %r4, 928(%r3)
	std %r4, 808(%r3)
	ld %r4, 936(%r3)
	std %r4, 816(%r3)
	ld %r4, 944(%r3)
	std %r4, 824(%r3)
	ld %r4, 952(%r3)
	std %r4, 832(%r3)
	ld %r4, 960(%r3)
	std %r4, 840(%r3)
	ld %r4, 968(%r3)
	std %r4, 848(%r3)
	ld %r4, 976(%r3)
	std %r4, 856(%r3)
	ld %r4, 184(%r3)
	std %r4, 624(%r3)
	ld %r4, 192(%r3)
	std %r4, 632(%r3)
	ld %r4, 200(%r3)
	std %r4, 640(%r3)
	ld %r4, 208(%r3)
	std %r4, 648(%r3)
	ld %r4, 216(%r3)
	std %r4, 656(%r3)
	ld %r4, 264(%r3)
	std %r4, 664(%r3)
	ld %r4, 272(%r3)
	std %r4, 672(%r3)
	ld %r4, 280(%r3)
	std %r4, 680(%r3)
	ld %r4, 288(%r3)
	std %r4, 688(%r3)
	ld %r4, 296(%r3)
	std %r4, 696(%r3)
	ld %r4, 184(%r3)
	std %r4, 704(%r3)
	ld %r4, 192(%r3)
	std %r4, 712(%r3)
	ld %r4, 200(%r3)
	std %r4, 720(%r3)
	ld %r4, 208(%r3)
	std %r4, 728(%r3)
	ld %r4, 216(%r3)
	std %r4, 736(%r3)
	li %r31, 80
278:
	addi %r31, %r31, -1
	li %r4, 744
	li %r5, 624
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 984
	li %r5, 704
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 784
	li %r5, 664
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 704
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 744
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 944
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1144
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 864
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 904
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 864
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 824
	li %r5, 904
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1104
	li %r6, 744
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1144
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 784
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 744
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 784
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 744
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 944
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 904
	li %r5, 1144
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 864
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 904
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 864
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1104
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 944
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 824
	li %r5, 904
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 1144
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 1104
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1104
	li %r6, 744
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 784
	li %r5, 1144
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 1064
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 784
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 624
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 984
	li %r5, 824
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 704
	li %r5, 984
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 664
	li %r5, 784
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r5, 704(%r3)
	ld %r4, 712(%r3)
	or %r5, %r5, %r4
	ld %r4, 720(%r3)
	or %r5, %r5, %r4
	ld %r4, 728(%r3)
	or %r5, %r5, %r4
	ld %r4, 736(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	or %r10, %r5, %r5
	ld %r4, 264(%r3)
	ld %r5, 664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 272(%r3)
	ld %r5, 672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 280(%r3)
	ld %r5, 680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 288(%r3)
	ld %r5, 688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 296(%r3)
	ld %r5, 696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
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
	ld %r4, 744(%r3)
	ld %r5, 5056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 1
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 2
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 3
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 4
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 5
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 6
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 5880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 5888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 7
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 5896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 5904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 5912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 5920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 5928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 5936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 5944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 5952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 5960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 5968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 5976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 5984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 5992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 8
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 9
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 10
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 11
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 12
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 13
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 14
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r5, 15
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 744(%r3)
	ld %r5, 6856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 752(%r3)
	ld %r5, 6864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 760(%r3)
	ld %r5, 6872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 6880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 6888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 784(%r3)
	ld %r5, 6896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 792(%r3)
	ld %r5, 6904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 800(%r3)
	ld %r5, 6912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 808(%r3)
	ld %r5, 6920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 816(%r3)
	ld %r5, 6928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 824(%r3)
	ld %r5, 6936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 832(%r3)
	ld %r5, 6944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 840(%r3)
	ld %r5, 6952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 848(%r3)
	ld %r5, 6960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 856(%r3)
	ld %r5, 6968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	li %r4, 984
	li %r5, 624
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 664
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 704
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 624
	li %r6, 664
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 744
	li %r6, 784
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 624
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 664
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 784
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 864
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 864
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 944
	li %r5, 1024
	li %r6, 944
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 904
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 1104
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 1184
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 944
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 864(%r3)
	std %r4, 624(%r3)
	ld %r4, 872(%r3)
	std %r4, 632(%r3)
	ld %r4, 880(%r3)
	std %r4, 640(%r3)
	ld %r4, 888(%r3)
	std %r4, 648(%r3)
	ld %r4, 896(%r3)
	std %r4, 656(%r3)
	ld %r4, 904(%r3)
	std %r4, 664(%r3)
	ld %r4, 912(%r3)
	std %r4, 672(%r3)
	ld %r4, 920(%r3)
	std %r4, 680(%r3)
	ld %r4, 928(%r3)
	std %r4, 688(%r3)
	ld %r4, 936(%r3)
	std %r4, 696(%r3)
	ld %r4, 944(%r3)
	std %r4, 704(%r3)
	ld %r4, 952(%r3)
	std %r4, 712(%r3)
	ld %r4, 960(%r3)
	std %r4, 720(%r3)
	ld %r4, 968(%r3)
	std %r4, 728(%r3)
	ld %r4, 976(%r3)
	std %r4, 736(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 984
	li %r5, 1704
	li %r6, 624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1744
	li %r6, 664
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1064
	li %r5, 1544
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1104
	li %r5, 1704
	li %r6, 1744
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 624
	li %r6, 664
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 984
	li %r6, 1024
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1104
	li %r5, 1104
	li %r6, 1144
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1144
	li %r5, 1704
	li %r6, 1544
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 624
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1184
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1184
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1184
	li %r5, 1744
	li %r6, 1544
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 664
	li %r6, 704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1184
	li %r5, 1184
	li %r6, 744
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 824
	li %r5, 304
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 344
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 744
	li %r5, 1024
	li %r6, 824
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 824
	li %r5, 1024
	li %r6, 824
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 784
	li %r5, 744
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 344
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1064
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 1064
	li %r5, 304
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1144
	li %r5, 1144
	li %r6, 1064
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1024
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 784
	li %r5, 784
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 984
	li %r5, 1184
	li %r6, 1144
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 1104
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 744
	li %r5, 744
	li %r6, 984
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 984
	li %r5, 1104
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 1184
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 824
	li %r6, 984
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r4, 744(%r3)
	std %r4, 624(%r3)
	ld %r4, 752(%r3)
	std %r4, 632(%r3)
	ld %r4, 760(%r3)
	std %r4, 640(%r3)
	ld %r4, 768(%r3)
	std %r4, 648(%r3)
	ld %r4, 776(%r3)
	std %r4, 656(%r3)
	ld %r4, 784(%r3)
	std %r4, 664(%r3)
	ld %r4, 792(%r3)
	std %r4, 672(%r3)
	ld %r4, 800(%r3)
	std %r4, 680(%r3)
	ld %r4, 808(%r3)
	std %r4, 688(%r3)
	ld %r4, 816(%r3)
	std %r4, 696(%r3)
	ld %r4, 824(%r3)
	std %r4, 704(%r3)
	ld %r4, 832(%r3)
	std %r4, 712(%r3)
	ld %r4, 840(%r3)
	std %r4, 720(%r3)
	ld %r4, 848(%r3)
	std %r4, 728(%r3)
	ld %r4, 856(%r3)
	std %r4, 736(%r3)
	ld %r4, 704(%r3)
	std %r4, 744(%r3)
	ld %r4, 712(%r3)
	std %r4, 752(%r3)
	ld %r4, 720(%r3)
	std %r4, 760(%r3)
	ld %r4, 728(%r3)
	std %r4, 768(%r3)
	ld %r4, 736(%r3)
	std %r4, 776(%r3)
	li %r4, 1064
	li %r5, 704
	li %r6, 704
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 784
	li %r5, 744
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 824
	li %r5, 784
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 864
	li %r5, 824
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 904
	li %r5, 864
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 944
	li %r5, 904
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 984
	li %r5, 944
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1024
	li %r5, 984
	li %r6, 1064
	bl {vg_brainpoolp320r1_mul_mod_p}
	ld %r4, 984(%r3)
	std %r4, 1224(%r3)
	ld %r4, 992(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1000(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1008(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1016(%r3)
	std %r4, 1256(%r3)
	li %r31, 6
279:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
280:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
281:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
282:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
283:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 11
284:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
285:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
286:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
287:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
288:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
289:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
290:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 1
291:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
292:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
293:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
294:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
295:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
296:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
297:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
298:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 12
299:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
2100:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2101:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2102:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2103:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2103b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2104:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2104b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
2105:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2105b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2106:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2106b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2107:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2107b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2108:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2108b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2109:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2109b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
2110:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2110b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2111:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2111b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
2112:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2112b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 10
2113:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2113b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2114:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2114b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
2115:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2115b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
2116:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2116b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2117:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2117b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2118:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2118b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
2119:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2119b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2120:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2120b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2121:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2121b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
2122:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2122b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2123:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2123b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2124:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2124b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2125:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2125b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2126:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2126b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2127:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2127b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2128:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2128b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
2129:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2129b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
2130:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2130b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
2131:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2131b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 9
2132:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2132b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
2133:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2133b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2134:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2134b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 1
2135:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2135b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2136:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2136b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2137:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2137b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2138:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2138b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
2139:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2139b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
2140:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2140b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
2141:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2141b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1424
	li %r5, 624
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1464
	li %r5, 1424
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1584
	li %r5, 1464
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1664
	li %r5, 1584
	li %r6, 1624
	bl {vg_brainpoolp320r1_sub_mod_n}
	ld %r5, 704(%r3)
	ld %r4, 712(%r3)
	or %r5, %r5, %r4
	ld %r4, 720(%r3)
	or %r5, %r5, %r4
	ld %r4, 728(%r3)
	or %r5, %r5, %r4
	ld %r4, 736(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r5, 1664(%r3)
	ld %r4, 1672(%r3)
	or %r5, %r5, %r4
	ld %r4, 1680(%r3)
	or %r5, %r5, %r4
	ld %r4, 1688(%r3)
	or %r5, %r5, %r4
	ld %r4, 1696(%r3)
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
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r10, 1824(%r3)
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
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_ecdsa_brainpoolp320r1_sign:
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
	li %r9, 40
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 344
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
	li %r8, 36
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, 17605
	ori %r12, %r12, 37649
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 32
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, -31087
	ori %r12, %r12, 21851
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -4474
	ori %r12, %r12, 22761
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, 11592
	ori %r12, %r12, 11975
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -18801
	ori %r12, %r12, 4771
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -1649
	ori %r12, %r12, 53157
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -11775
	ori %r12, %r12, 57445
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, -7876
	ori %r12, %r12, 30814
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 128(%r11)
	lis %r12, 14012
	ori %r12, %r12, 20407
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 64(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 132(%r11)
	lis %r12, -11426
	ori %r12, %r12, 18208
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 68(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 268
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 264
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 260
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 256
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 252
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 248
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 244
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 240
	stwbrx %r7, %r11, %r12
	lwz %r7, 128(%r11)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 236
	stwbrx %r7, %r11, %r12
	lwz %r7, 132(%r11)
	lwz %r8, 68(%r11)
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
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2333(%r9)
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
	li %r6, 81
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
	addi %r5, %r5, 81
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
	li %r6, 81
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
	addi %r5, %r5, 81
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
	li %r9, 128
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
	li %r10, 40
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
	bl {vg_ecdsa_brainpoolp320r1_sign_k}
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
