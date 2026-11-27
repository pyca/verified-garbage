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
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 17
	addi %r9, %r3, 0
25:
	addi %r31, %r31, -1
	ld %r11, 0(%r4)
	std %r11, 64(%r9)
	ld %r11, 8(%r4)
	std %r11, 72(%r9)
	ld %r11, 16(%r4)
	std %r11, 80(%r9)
	ld %r11, 24(%r4)
	std %r11, 88(%r9)
	ld %r11, 32(%r4)
	std %r11, 96(%r9)
	addi %r4, %r4, 40
	addi %r9, %r9, 40
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1824(%r3)
	or %r12, %r5, %r5
	li %r31, 40
26:
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
	bne %cr0, 26b
	li %r31, 40
27:
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
	bne %cr0, 27b
	li %r31, 40
28:
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
	bne %cr0, 28b
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
	bl {vg_brainpoolp320r1_validate}
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
	bl {vg_brainpoolp320r1_inv_mod_n}
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
29:
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
	bne %cr0, 29b
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
210:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -45
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
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
	bne %cr0, 210b
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
216:
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
	bne %cr0, 216b
	bl {vg_brainpoolp320r1_windows}
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
	bl {vg_brainpoolp320r1_inv_mod_p}
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
