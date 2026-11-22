// The functions of `src/ec_brainpoolp320r1_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp320r1_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1336(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1344(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1352(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1360(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1368(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1376(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1416(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 85
20:
	addi %r31, %r31, -1
	rldicr %r8, %r31, 3, 60
	add %r9, %r4, %r8
	ld %r11, 0(%r9)
	add %r9, %r3, %r8
	std %r11, 64(%r9)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1824(%r3)
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
	bl {vg_brainpoolp320r1_validate}
	ld %r10, 1824(%r3)
	ld %r4, 1504(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1384(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 1392(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1400(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1408(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1416(%r3)
	and %r4, %r4, %r10
	li %r6, 1
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

vg_ec_brainpoolp320r1_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1336(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1344(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1352(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1360(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1368(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1376(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1416(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 85
20:
	addi %r31, %r31, -1
	rldicr %r8, %r31, 3, 60
	add %r9, %r4, %r8
	ld %r11, 0(%r9)
	add %r9, %r3, %r8
	std %r11, 64(%r9)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1824(%r3)
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
	lbz %r4, 0(%r12)
	std %r4, 1344(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
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
	li %r4, 1424
	li %r5, 1384
	li %r6, 1624
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
	lis %r11, 31852
	ori %r11, %r11, 52106
	stw %r11, 544(%r3)
	lis %r11, 16181
	ori %r11, %r11, 1196
	stw %r11, 548(%r3)
	lis %r11, 7716
	ori %r11, %r11, 64266
	stw %r11, 552(%r3)
	lis %r11, -11292
	ori %r11, %r11, 44667
	stw %r11, 556(%r3)
	lis %r11, -16963
	ori %r11, %r11, 891
	stw %r11, 560(%r3)
	lis %r11, 32355
	ori %r11, %r11, 62441
	stw %r11, 564(%r3)
	lis %r11, -19328
	ori %r11, %r11, 30745
	stw %r11, 568(%r3)
	lis %r11, -1969
	ori %r11, %r11, 7703
	stw %r11, 572(%r3)
	lis %r11, 3503
	ori %r11, %r11, 5101
	stw %r11, 576(%r3)
	lis %r11, 13527
	ori %r11, %r11, 37320
	stw %r11, 580(%r3)
	li %r31, 40
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 544(%r4)
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
	bne %cr0, 21b
	ld %r4, 264(%r3)
	std %r4, 1224(%r3)
	ld %r4, 272(%r3)
	std %r4, 1232(%r3)
	ld %r4, 280(%r3)
	std %r4, 1240(%r3)
	ld %r4, 288(%r3)
	std %r4, 1248(%r3)
	ld %r4, 296(%r3)
	std %r4, 1256(%r3)
	li %r31, 320
22:
	addi %r31, %r31, -1
	li %r4, 1224
	li %r5, 1224
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1224
	li %r6, 1744
	bl {vg_brainpoolp320r1_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4736(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1224(%r3)
	ld %r5, 1264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1224(%r3)
	ld %r4, 1232(%r3)
	ld %r5, 1272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1232(%r3)
	ld %r4, 1240(%r3)
	ld %r5, 1280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1240(%r3)
	ld %r4, 1248(%r3)
	ld %r5, 1288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1248(%r3)
	ld %r4, 1256(%r3)
	ld %r5, 1296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1256(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1504
	li %r5, 1224
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1544
	li %r5, 184
	li %r6, 1504
	bl {vg_brainpoolp320r1_sub_mod_p}
	ld %r4, 1504(%r3)
	ld %r5, 1344(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 1504(%r3)
	ld %r5, 1544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1504(%r3)
	ld %r4, 1512(%r3)
	ld %r5, 1552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1512(%r3)
	ld %r4, 1520(%r3)
	ld %r5, 1560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1520(%r3)
	ld %r4, 1528(%r3)
	ld %r5, 1568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1528(%r3)
	ld %r4, 1536(%r3)
	ld %r5, 1576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1536(%r3)
	li %r4, 1464
	li %r5, 1504
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1704
	li %r5, 1464
	li %r6, 1464
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1584
	li %r5, 1704
	li %r6, 1744
	bl {vg_brainpoolp320r1_sub_mod_p}
	ld %r5, 1584(%r3)
	ld %r4, 1592(%r3)
	or %r5, %r5, %r4
	ld %r4, 1600(%r3)
	or %r5, %r5, %r4
	ld %r4, 1608(%r3)
	or %r5, %r5, %r4
	ld %r4, 1616(%r3)
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
	ld %r4, 1504(%r3)
	ld %r5, 1344(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r10, 1824(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1384(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 1392(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1400(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1408(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1416(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 1504(%r3)
	and %r4, %r4, %r10
	li %r6, 73
	stdbrx %r4, %r14, %r6
	ld %r4, 1512(%r3)
	and %r4, %r4, %r10
	li %r6, 65
	stdbrx %r4, %r14, %r6
	ld %r4, 1520(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 1528(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 1536(%r3)
	and %r4, %r4, %r10
	li %r6, 41
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
