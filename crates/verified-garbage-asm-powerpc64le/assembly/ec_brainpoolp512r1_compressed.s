// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2232(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	ld %r11, 48(%r4)
	std %r11, 112(%r9)
	ld %r11, 56(%r4)
	std %r11, 120(%r9)
	addi %r4, %r4, 64
	addi %r9, %r9, 64
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2880(%r3)
	lis %r11, 24920
	ori %r11, %r11, 61957
	stw %r11, 2560(%r3)
	lis %r11, 18861
	ori %r11, %r11, 5194
	stw %r11, 2564(%r3)
	lis %r11, 10005
	ori %r11, %r11, 30981
	stw %r11, 2568(%r3)
	lis %r11, 31039
	ori %r11, %r11, 45360
	stw %r11, 2572(%r3)
	lis %r11, -28582
	ori %r11, %r11, 65491
	stw %r11, 2576(%r3)
	lis %r11, 21431
	ori %r11, %r11, 63932
	stw %r11, 2580(%r3)
	lis %r11, -31919
	ori %r11, %r11, 18981
	stw %r11, 2584(%r3)
	lis %r11, -7999
	ori %r11, %r11, 39543
	stw %r11, 2588(%r3)
	lis %r11, -10871
	ori %r11, %r11, 32855
	stw %r11, 2592(%r3)
	lis %r11, 6472
	ori %r11, %r11, 28632
	stw %r11, 2596(%r3)
	lis %r11, -11221
	ori %r11, %r11, 65411
	stw %r11, 2600(%r3)
	lis %r11, -24211
	ori %r11, %r11, 43615
	stw %r11, 2604(%r3)
	lis %r11, 8278
	ori %r11, %r11, 61132
	stw %r11, 2608(%r3)
	lis %r11, 8238
	ori %r11, %r11, 6464
	stw %r11, 2612(%r3)
	lis %r11, -22017
	ori %r11, %r11, 25680
	stw %r11, 2616(%r3)
	lis %r11, 15436
	ori %r11, %r11, 40197
	stw %r11, 2620(%r3)
	lis %r11, 8425
	ori %r11, %r11, 10804
	stw %r11, 2624(%r3)
	lis %r11, 20606
	ori %r11, %r11, 33686
	stw %r11, 2628(%r3)
	lis %r11, -6770
	ori %r11, %r11, 23092
	stw %r11, 2632(%r3)
	lis %r11, 155
	ori %r11, %r11, 25543
	stw %r11, 2636(%r3)
	lis %r11, 11655
	ori %r11, %r11, 9386
	stw %r11, 2640(%r3)
	lis %r11, -7829
	ori %r11, %r11, 42070
	stw %r11, 2644(%r3)
	lis %r11, -26505
	ori %r11, %r11, 48642
	stw %r11, 2648(%r3)
	lis %r11, -14530
	ori %r11, %r11, 12520
	stw %r11, 2652(%r3)
	lis %r11, -478
	ori %r11, %r11, 9267
	stw %r11, 2656(%r3)
	lis %r11, -26656
	ori %r11, %r11, 3171
	stw %r11, 2660(%r3)
	lis %r11, 27927
	ori %r11, %r11, 55325
	stw %r11, 2664(%r3)
	lis %r11, -13350
	ori %r11, %r11, 22444
	stw %r11, 2668(%r3)
	lis %r11, 2997
	ori %r11, %r11, 43682
	stw %r11, 2672(%r3)
	lis %r11, 25635
	ori %r11, %r11, 4773
	stw %r11, 2676(%r3)
	lis %r11, 18206
	ori %r11, %r11, 36519
	stw %r11, 2680(%r3)
	lis %r11, 27210
	ori %r11, %r11, 43956
	stw %r11, 2684(%r3)
	addi %r6, %r12, 1
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2232(%r3)
	addi %r6, %r6, 64
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2368(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2376(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2384(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2392(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2400(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2408(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2416(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2424(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2176(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2180(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2184(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2188(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2192(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2196(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2200(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2204(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2208(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2212(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2216(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2220(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2224(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2228(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2232(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2236(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2368(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2372(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2376(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2380(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2384(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2388(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2392(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2396(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2400(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2404(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2408(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2412(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2416(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2420(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2424(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2428(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	bl {vg_brainpoolp512r1_validate}
	ld %r10, 2880(%r3)
	ld %r4, 2368(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2176(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 2184(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 2192(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 2200(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 2208(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 2216(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 2224(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 2232(%r3)
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

vg_ec_brainpoolp512r1_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2232(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
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
	ld %r11, 48(%r4)
	std %r11, 112(%r9)
	ld %r11, 56(%r4)
	std %r11, 120(%r9)
	addi %r4, %r4, 64
	addi %r9, %r9, 64
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2880(%r3)
	lis %r11, 24920
	ori %r11, %r11, 61957
	stw %r11, 2560(%r3)
	lis %r11, 18861
	ori %r11, %r11, 5194
	stw %r11, 2564(%r3)
	lis %r11, 10005
	ori %r11, %r11, 30981
	stw %r11, 2568(%r3)
	lis %r11, 31039
	ori %r11, %r11, 45360
	stw %r11, 2572(%r3)
	lis %r11, -28582
	ori %r11, %r11, 65491
	stw %r11, 2576(%r3)
	lis %r11, 21431
	ori %r11, %r11, 63932
	stw %r11, 2580(%r3)
	lis %r11, -31919
	ori %r11, %r11, 18981
	stw %r11, 2584(%r3)
	lis %r11, -7999
	ori %r11, %r11, 39543
	stw %r11, 2588(%r3)
	lis %r11, -10871
	ori %r11, %r11, 32855
	stw %r11, 2592(%r3)
	lis %r11, 6472
	ori %r11, %r11, 28632
	stw %r11, 2596(%r3)
	lis %r11, -11221
	ori %r11, %r11, 65411
	stw %r11, 2600(%r3)
	lis %r11, -24211
	ori %r11, %r11, 43615
	stw %r11, 2604(%r3)
	lis %r11, 8278
	ori %r11, %r11, 61132
	stw %r11, 2608(%r3)
	lis %r11, 8238
	ori %r11, %r11, 6464
	stw %r11, 2612(%r3)
	lis %r11, -22017
	ori %r11, %r11, 25680
	stw %r11, 2616(%r3)
	lis %r11, 15436
	ori %r11, %r11, 40197
	stw %r11, 2620(%r3)
	lis %r11, 8425
	ori %r11, %r11, 10804
	stw %r11, 2624(%r3)
	lis %r11, 20606
	ori %r11, %r11, 33686
	stw %r11, 2628(%r3)
	lis %r11, -6770
	ori %r11, %r11, 23092
	stw %r11, 2632(%r3)
	lis %r11, 155
	ori %r11, %r11, 25543
	stw %r11, 2636(%r3)
	lis %r11, 11655
	ori %r11, %r11, 9386
	stw %r11, 2640(%r3)
	lis %r11, -7829
	ori %r11, %r11, 42070
	stw %r11, 2644(%r3)
	lis %r11, -26505
	ori %r11, %r11, 48642
	stw %r11, 2648(%r3)
	lis %r11, -14530
	ori %r11, %r11, 12520
	stw %r11, 2652(%r3)
	lis %r11, -478
	ori %r11, %r11, 9267
	stw %r11, 2656(%r3)
	lis %r11, -26656
	ori %r11, %r11, 3171
	stw %r11, 2660(%r3)
	lis %r11, 27927
	ori %r11, %r11, 55325
	stw %r11, 2664(%r3)
	lis %r11, -13350
	ori %r11, %r11, 22444
	stw %r11, 2668(%r3)
	lis %r11, 2997
	ori %r11, %r11, 43682
	stw %r11, 2672(%r3)
	lis %r11, 25635
	ori %r11, %r11, 4773
	stw %r11, 2676(%r3)
	lis %r11, 18206
	ori %r11, %r11, 36519
	stw %r11, 2680(%r3)
	lis %r11, 27210
	ori %r11, %r11, 43956
	stw %r11, 2684(%r3)
	addi %r6, %r12, 1
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2232(%r3)
	lbz %r4, 0(%r12)
	std %r4, 2112(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2176(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2180(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2184(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2188(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2192(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2196(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2200(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2204(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2208(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2212(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2216(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2220(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2224(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2228(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2232(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2236(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r4, 2240
	li %r5, 2176
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2240
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2752
	li %r5, 2688
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 448
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2752
	li %r6, 2688
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2752
	li %r5, 2496
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_p}
	lis %r11, -27122
	ori %r11, %r11, 37437
	stw %r11, 832(%r3)
	lis %r11, 18986
	ori %r11, %r11, 38933
	stw %r11, 836(%r3)
	lis %r11, -13472
	ori %r11, %r11, 45473
	stw %r11, 840(%r3)
	lis %r11, -30176
	ori %r11, %r11, 32715
	stw %r11, 844(%r3)
	lis %r11, -18008
	ori %r11, %r11, 57401
	stw %r11, 848(%r3)
	lis %r11, -21581
	ori %r11, %r11, 26698
	stw %r11, 852(%r3)
	lis %r11, 9969
	ori %r11, %r11, 39440
	stw %r11, 856(%r3)
	lis %r11, 24403
	ori %r11, %r11, 26304
	stw %r11, 860(%r3)
	lis %r11, -25588
	ori %r11, %r11, 49692
	stw %r11, 864(%r3)
	lis %r11, -19048
	ori %r11, %r11, 59186
	stw %r11, 868(%r3)
	lis %r11, -4878
	ori %r11, %r11, 29827
	stw %r11, 872(%r3)
	lis %r11, -3380
	ori %r11, %r11, 9068
	stw %r11, 876(%r3)
	lis %r11, -29454
	ori %r11, %r11, 32513
	stw %r11, 880(%r3)
	lis %r11, -12299
	ori %r11, %r11, 14763
	stw %r11, 884(%r3)
	lis %r11, 14074
	ori %r11, %r11, 28962
	stw %r11, 888(%r3)
	lis %r11, 10935
	ori %r11, %r11, 26478
	stw %r11, 892(%r3)
	li %r31, 64
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 832(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5120(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5121(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5122(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5123(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5124(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5125(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5126(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5127(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	ld %r4, 384(%r3)
	std %r4, 1920(%r3)
	ld %r4, 392(%r3)
	std %r4, 1928(%r3)
	ld %r4, 400(%r3)
	std %r4, 1936(%r3)
	ld %r4, 408(%r3)
	std %r4, 1944(%r3)
	ld %r4, 416(%r3)
	std %r4, 1952(%r3)
	ld %r4, 424(%r3)
	std %r4, 1960(%r3)
	ld %r4, 432(%r3)
	std %r4, 1968(%r3)
	ld %r4, 440(%r3)
	std %r4, 1976(%r3)
	li %r31, 512
22:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1984
	li %r5, 1920
	li %r6, 2752
	bl {vg_brainpoolp512r1_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 5120(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1920(%r3)
	ld %r5, 1984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1920(%r3)
	ld %r4, 1928(%r3)
	ld %r5, 1992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1928(%r3)
	ld %r4, 1936(%r3)
	ld %r5, 2000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1936(%r3)
	ld %r4, 1944(%r3)
	ld %r5, 2008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1944(%r3)
	ld %r4, 1952(%r3)
	ld %r5, 2016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1952(%r3)
	ld %r4, 1960(%r3)
	ld %r5, 2024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1960(%r3)
	ld %r4, 1968(%r3)
	ld %r5, 2032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1968(%r3)
	ld %r4, 1976(%r3)
	ld %r5, 2040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1976(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 2368
	li %r5, 1920
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2432
	li %r5, 256
	li %r6, 2368
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r4, 2368(%r3)
	ld %r5, 2112(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 2368(%r3)
	ld %r5, 2432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2368(%r3)
	ld %r4, 2376(%r3)
	ld %r5, 2440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2376(%r3)
	ld %r4, 2384(%r3)
	ld %r5, 2448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2384(%r3)
	ld %r4, 2392(%r3)
	ld %r5, 2456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2392(%r3)
	ld %r4, 2400(%r3)
	ld %r5, 2464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2400(%r3)
	ld %r4, 2408(%r3)
	ld %r5, 2472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2408(%r3)
	ld %r4, 2416(%r3)
	ld %r5, 2480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2416(%r3)
	ld %r4, 2424(%r3)
	ld %r5, 2488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2424(%r3)
	li %r4, 2304
	li %r5, 2368
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2304
	li %r6, 2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2688
	li %r6, 2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r5, 2496(%r3)
	ld %r4, 2504(%r3)
	or %r5, %r5, %r4
	ld %r4, 2512(%r3)
	or %r5, %r5, %r4
	ld %r4, 2520(%r3)
	or %r5, %r5, %r4
	ld %r4, 2528(%r3)
	or %r5, %r5, %r4
	ld %r4, 2536(%r3)
	or %r5, %r5, %r4
	ld %r4, 2544(%r3)
	or %r5, %r5, %r4
	ld %r4, 2552(%r3)
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
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r4, 2368(%r3)
	ld %r5, 2112(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2176(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 2184(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 2192(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 2200(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 2208(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 2216(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 2224(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 2232(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 2368(%r3)
	and %r4, %r4, %r10
	li %r6, 121
	stdbrx %r4, %r14, %r6
	ld %r4, 2376(%r3)
	and %r4, %r4, %r10
	li %r6, 113
	stdbrx %r4, %r14, %r6
	ld %r4, 2384(%r3)
	and %r4, %r4, %r10
	li %r6, 105
	stdbrx %r4, %r14, %r6
	ld %r4, 2392(%r3)
	and %r4, %r4, %r10
	li %r6, 97
	stdbrx %r4, %r14, %r6
	ld %r4, 2400(%r3)
	and %r4, %r4, %r10
	li %r6, 89
	stdbrx %r4, %r14, %r6
	ld %r4, 2408(%r3)
	and %r4, %r4, %r10
	li %r6, 81
	stdbrx %r4, %r14, %r6
	ld %r4, 2416(%r3)
	and %r4, %r4, %r10
	li %r6, 73
	stdbrx %r4, %r14, %r6
	ld %r4, 2424(%r3)
	and %r4, %r4, %r10
	li %r6, 65
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
