// The functions of `src/ec_p384_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p384_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1592(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1600(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1608(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1616(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1624(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1632(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1640(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1688(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P384_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P384_FRAME_CONSTS}
	mtlr %r11
	li %r31, 17
	addi %r9, %r3, 0
20:
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
	ld %r11, 40(%r4)
	std %r11, 104(%r9)
	addi %r4, %r4, 48
	addi %r9, %r9, 48
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2176(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1936(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1940(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1944(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1956(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1960(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1964(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1968(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1972(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1976(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1980(%r3)
	lis %r11, -25279
	ori %r11, %r11, 11724
	stw %r11, 1984(%r3)
	lis %r11, 2065
	ori %r11, %r11, 34929
	stw %r11, 1988(%r3)
	lis %r11, 31308
	ori %r11, %r11, 13036
	stw %r11, 1992(%r3)
	lis %r11, -2263
	ori %r11, %r11, 44504
	stw %r11, 1996(%r3)
	lis %r11, 6432
	ori %r11, %r11, 558
	stw %r11, 2000(%r3)
	lis %r11, 30706
	ori %r11, %r11, 8347
	stw %r11, 2004(%r3)
	lis %r11, -27501
	ori %r11, %r11, 35554
	stw %r11, 2008(%r3)
	lis %r11, -7369
	ori %r11, %r11, 19438
	stw %r11, 2012(%r3)
	lis %r11, 7938
	ori %r11, %r11, 8340
	stw %r11, 2016(%r3)
	lis %r11, -18901
	ori %r11, %r11, 8692
	stw %r11, 2020(%r3)
	lis %r11, 24655
	ori %r11, %r11, 49145
	stw %r11, 2024(%r3)
	lis %r11, -13048
	ori %r11, %r11, 4427
	stw %r11, 2028(%r3)
	addi %r6, %r12, 1
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1688(%r3)
	addi %r6, %r6, 48
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1792(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1800(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1808(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1816(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1824(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1832(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1648(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1652(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1656(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1660(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1664(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1668(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1672(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1676(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1680(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1684(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1688(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1692(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1792(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1796(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1800(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1804(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1808(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1812(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1816(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1820(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1824(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1828(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1832(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1836(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	bl {vg_p384_validate}
	ld %r10, 2176(%r3)
	ld %r4, 1792(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1648(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 1656(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 1664(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1672(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1680(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1688(%r3)
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

vg_ec_p384_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1592(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1600(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1608(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1616(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1624(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1632(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1640(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1688(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P384_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P384_FRAME_CONSTS}
	mtlr %r11
	li %r31, 17
	addi %r9, %r3, 0
20:
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
	ld %r11, 40(%r4)
	std %r11, 104(%r9)
	addi %r4, %r4, 48
	addi %r9, %r9, 48
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2176(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1936(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1940(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1944(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1956(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1960(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1964(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1968(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1972(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1976(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1980(%r3)
	lis %r11, -25279
	ori %r11, %r11, 11724
	stw %r11, 1984(%r3)
	lis %r11, 2065
	ori %r11, %r11, 34929
	stw %r11, 1988(%r3)
	lis %r11, 31308
	ori %r11, %r11, 13036
	stw %r11, 1992(%r3)
	lis %r11, -2263
	ori %r11, %r11, 44504
	stw %r11, 1996(%r3)
	lis %r11, 6432
	ori %r11, %r11, 558
	stw %r11, 2000(%r3)
	lis %r11, 30706
	ori %r11, %r11, 8347
	stw %r11, 2004(%r3)
	lis %r11, -27501
	ori %r11, %r11, 35554
	stw %r11, 2008(%r3)
	lis %r11, -7369
	ori %r11, %r11, 19438
	stw %r11, 2012(%r3)
	lis %r11, 7938
	ori %r11, %r11, 8340
	stw %r11, 2016(%r3)
	lis %r11, -18901
	ori %r11, %r11, 8692
	stw %r11, 2020(%r3)
	lis %r11, 24655
	ori %r11, %r11, 49145
	stw %r11, 2024(%r3)
	lis %r11, -13048
	ori %r11, %r11, 4427
	stw %r11, 2028(%r3)
	addi %r6, %r12, 1
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1688(%r3)
	lbz %r4, 0(%r12)
	std %r4, 1600(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1648(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1652(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1656(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1660(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1664(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1668(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1672(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1676(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1680(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1684(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1688(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1692(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r4, 1696
	li %r5, 1648
	li %r6, 1936
	bl {vg_p384_mul_mod_p}
	li %r4, 2032
	li %r5, 1696
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 2080
	li %r5, 2032
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 2032
	li %r5, 352
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 1888
	li %r5, 2080
	li %r6, 2032
	bl {vg_p384_add_mod_p}
	li %r4, 2080
	li %r5, 1888
	li %r6, 1984
	bl {vg_p384_add_mod_p}
	lis %r11, 16384
	ori %r11, %r11, 0
	stw %r11, 640(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 644(%r3)
	lis %r11, -16384
	ori %r11, %r11, 0
	stw %r11, 648(%r3)
	lis %r11, -16385
	ori %r11, %r11, 65535
	stw %r11, 652(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 656(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 660(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 664(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 668(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 672(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 676(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 680(%r3)
	lis %r11, 16383
	ori %r11, %r11, 65535
	stw %r11, 684(%r3)
	li %r31, 48
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 640(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4864(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4865(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4866(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4867(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4868(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4869(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4870(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4871(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	ld %r4, 304(%r3)
	std %r4, 1456(%r3)
	ld %r4, 312(%r3)
	std %r4, 1464(%r3)
	ld %r4, 320(%r3)
	std %r4, 1472(%r3)
	ld %r4, 328(%r3)
	std %r4, 1480(%r3)
	ld %r4, 336(%r3)
	std %r4, 1488(%r3)
	ld %r4, 344(%r3)
	std %r4, 1496(%r3)
	li %r31, 384
22:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1504
	li %r5, 1456
	li %r6, 2080
	bl {vg_p384_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4864(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1456(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	ld %r4, 1472(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r4, 1480(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1480(%r3)
	ld %r4, 1488(%r3)
	ld %r5, 1536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1488(%r3)
	ld %r4, 1496(%r3)
	ld %r5, 1544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1496(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1792
	li %r5, 1456
	li %r6, 256
	bl {vg_p384_mul_mod_p}
	li %r4, 1840
	li %r5, 208
	li %r6, 1792
	bl {vg_p384_sub_mod_p}
	ld %r4, 1792(%r3)
	ld %r5, 1600(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 1792(%r3)
	ld %r5, 1840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1792(%r3)
	ld %r4, 1800(%r3)
	ld %r5, 1848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1800(%r3)
	ld %r4, 1808(%r3)
	ld %r5, 1856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1808(%r3)
	ld %r4, 1816(%r3)
	ld %r5, 1864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1816(%r3)
	ld %r4, 1824(%r3)
	ld %r5, 1872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r4, 1832(%r3)
	ld %r5, 1880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1832(%r3)
	li %r4, 1744
	li %r5, 1792
	li %r6, 1936
	bl {vg_p384_mul_mod_p}
	li %r4, 2032
	li %r5, 1744
	li %r6, 1744
	bl {vg_p384_mul_mod_p}
	li %r4, 1888
	li %r5, 2032
	li %r6, 2080
	bl {vg_p384_sub_mod_p}
	ld %r5, 1888(%r3)
	ld %r4, 1896(%r3)
	or %r5, %r5, %r4
	ld %r4, 1904(%r3)
	or %r5, %r5, %r4
	ld %r4, 1912(%r3)
	or %r5, %r5, %r4
	ld %r4, 1920(%r3)
	or %r5, %r5, %r4
	ld %r4, 1928(%r3)
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
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r4, 1792(%r3)
	ld %r5, 1600(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r10, 2176(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1648(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 1656(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 1664(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1672(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1680(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1688(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 1792(%r3)
	and %r4, %r4, %r10
	li %r6, 89
	stdbrx %r4, %r14, %r6
	ld %r4, 1800(%r3)
	and %r4, %r4, %r10
	li %r6, 81
	stdbrx %r4, %r14, %r6
	ld %r4, 1808(%r3)
	and %r4, %r4, %r10
	li %r6, 73
	stdbrx %r4, %r14, %r6
	ld %r4, 1816(%r3)
	and %r4, %r4, %r10
	li %r6, 65
	stdbrx %r4, %r14, %r6
	ld %r4, 1824(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 1832(%r3)
	and %r4, %r4, %r10
	li %r6, 49
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
