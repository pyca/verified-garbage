// The functions of `src/ecdh_brainpoolp512r1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp512r1:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 56
	ldbrx %r8, %r4, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r4, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r4, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r4, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r4, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r4, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 2232(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 136
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
	std %r4, 2880(%r3)
	or %r12, %r5, %r5
	li %r31, 64
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2048(%r4)
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
	bne %cr0, 21b
	li %r31, 64
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 832(%r4)
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
	bne %cr0, 22b
	li %r31, 64
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 896(%r4)
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
	bne %cr0, 23b
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
	bl {vg_brainpoolp512r1_windows}
	bl {vg_brainpoolp512r1_inv_mod_p}
	li %r4, 2240
	li %r5, 960
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2304
	li %r5, 2240
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2112(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2116(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2120(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2124(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2128(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2132(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2136(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2140(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2144(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2148(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2152(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2156(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2160(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2164(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2168(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2172(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2112(%r3)
	ld %r4, 2120(%r3)
	or %r5, %r5, %r4
	ld %r4, 2128(%r3)
	or %r5, %r5, %r4
	ld %r4, 2136(%r3)
	or %r5, %r5, %r4
	ld %r4, 2144(%r3)
	or %r5, %r5, %r4
	ld %r4, 2152(%r3)
	or %r5, %r5, %r4
	ld %r4, 2160(%r3)
	or %r5, %r5, %r4
	ld %r4, 2168(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r5, 1088(%r3)
	ld %r4, 1096(%r3)
	or %r5, %r5, %r4
	ld %r4, 1104(%r3)
	or %r5, %r5, %r4
	ld %r4, 1112(%r3)
	or %r5, %r5, %r4
	ld %r4, 1120(%r3)
	or %r5, %r5, %r4
	ld %r4, 1128(%r3)
	or %r5, %r5, %r4
	ld %r4, 1136(%r3)
	or %r5, %r5, %r4
	ld %r4, 1144(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 2304(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 2312(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 2320(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 2328(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 2336(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 2344(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 2352(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 2360(%r3)
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
