// The functions of `src/internal/vg_ecdsa_brainpoolp320r1_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
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
	ldbrx %r8, %r5, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
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
23:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -45
	cmpldi %cr0, %r6, 0
	beq %cr0, 24f
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
	b 25f
24:
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
25:
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
26:
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
	bne %cr0, 26b
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
	beq %cr0, 27f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	addi %r10, %r4, -1
	b 28f
27:
	li %r10, 0
	addi %r10, %r10, -1
28:
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
	bne %cr0, 23b
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
29:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
210:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
211:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
212:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
213:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 11
214:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
215:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
216:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
217:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
218:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
219:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 1
221:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
222:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
223:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
224:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
225:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
226:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
227:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
228:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 12
229:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 8
230:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
231:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
234:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
235:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
236:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
237:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
238:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
239:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
240:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
241:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
242:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 10
243:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
244:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
245:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
246:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
247:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
248:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
249:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
250:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
251:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 3
252:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
253:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
254:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
255:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
256:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
257:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
258:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
259:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 6
260:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
261:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 9
262:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 5
263:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
264:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 1
265:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
266:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
267:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
268:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 4
269:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 7
270:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r31, 2
271:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
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
	li %r4, 1504
	li %r5, 1464
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_n}
	li %r4, 1544
	li %r5, 1304
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
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
	ld %r5, 1504(%r3)
	ld %r4, 1512(%r3)
	or %r5, %r5, %r4
	ld %r4, 1520(%r3)
	or %r5, %r5, %r4
	ld %r4, 1528(%r3)
	or %r5, %r5, %r4
	ld %r4, 1536(%r3)
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
272:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
273:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
274:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
275:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
276:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 11
277:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
278:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
279:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
280:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
281:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
282:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
283:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
284:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
285:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
286:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
287:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
288:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
289:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
290:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
291:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 12
292:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
293:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
294:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
295:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
296:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
297:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 2
298:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
299:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
2100:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2101:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
2102:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
2103:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2103b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
2104:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2104b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
2105:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2105b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2106:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2106b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
2107:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2107b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2108:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2108b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2109:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2109b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
2110:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2110b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 9
2111:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2111b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2112:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2112b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
2113:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2113b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2114:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2114b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2115:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2115b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2116:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2116b
	li %r4, 1224
	li %r5, 1224
	li %r6, 784
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2117:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2117b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2118:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2118b
	li %r4, 1224
	li %r5, 1224
	li %r6, 864
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
2119:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2119b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
2120:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2120b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
2121:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2121b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
2122:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2122b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2123:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2123b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2124:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2124b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 4
2125:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2125b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 5
2126:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2126b
	li %r4, 1224
	li %r5, 1224
	li %r6, 984
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 3
2127:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2127b
	li %r4, 1224
	li %r5, 1224
	li %r6, 824
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
2128:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2128b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
2129:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2129b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 7
2130:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2130b
	li %r4, 1224
	li %r5, 1224
	li %r6, 944
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 6
2131:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2131b
	li %r4, 1224
	li %r5, 1224
	li %r6, 904
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 1
2132:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2132b
	li %r4, 1224
	li %r5, 1224
	li %r6, 744
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r31, 8
2133:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2133b
	li %r4, 1224
	li %r5, 1224
	li %r6, 1024
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1584
	li %r5, 1504
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1624
	li %r5, 1344
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1664
	li %r5, 1384
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1704
	li %r5, 1584
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1704
	li %r5, 1704
	li %r6, 1664
	bl {vg_brainpoolp320r1_add_mod_n}
	li %r4, 1744
	li %r5, 1224
	li %r6, 1704
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1784
	li %r5, 1744
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r5, 1784(%r3)
	ld %r4, 1792(%r3)
	or %r5, %r5, %r4
	ld %r4, 1800(%r3)
	or %r5, %r5, %r4
	ld %r4, 1808(%r3)
	or %r5, %r5, %r4
	ld %r4, 1816(%r3)
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
	ld %r4, 1504(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1512(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1520(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1528(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1536(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 1784(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 1792(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	ld %r4, 1800(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 1808(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 1816(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
