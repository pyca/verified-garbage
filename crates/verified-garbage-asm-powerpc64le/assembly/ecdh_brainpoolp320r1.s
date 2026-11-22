// The functions of `src/ecdh_brainpoolp320r1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp320r1:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
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
20:
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
	bne %cr0, 20b
	li %r31, 40
21:
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
	bne %cr0, 21b
	li %r31, 40
22:
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
	bne %cr0, 22b
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
	addi %r6, %r12, 1
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
	lbz %r4, 0(%r12)
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
23:
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
	bne %cr0, 23b
	bl {vg_brainpoolp320r1_inv_mod_p}
	li %r4, 1424
	li %r5, 624
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1464
	li %r5, 1424
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1344(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1348(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1352(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1356(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1360(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1364(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1368(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1372(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1376(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1380(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1344(%r3)
	ld %r4, 1352(%r3)
	or %r5, %r5, %r4
	ld %r4, 1360(%r3)
	or %r5, %r5, %r4
	ld %r4, 1368(%r3)
	or %r5, %r5, %r4
	ld %r4, 1376(%r3)
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
	ld %r10, 1824(%r3)
	ld %r4, 1464(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1472(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1480(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1488(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1496(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	li %r0, 0
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
