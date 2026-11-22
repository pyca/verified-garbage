// The functions of `src/ecdh_p521.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p521:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P521_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P521_FRAME_CONSTS}
	mtlr %r11
	li %r31, 153
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
	std %r4, 3232(%r3)
	or %r12, %r5, %r5
	li %r31, 72
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2296(%r4)
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
	li %r31, 72
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 928(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4672(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4673(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4674(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4675(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4676(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4677(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4678(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4679(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 72
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1000(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5248(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5249(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5250(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5251(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5252(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5253(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5254(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5255(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2876(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2880(%r3)
	lis %r11, 0
	ori %r11, %r11, 16384
	stw %r11, 2884(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2888(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2924(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2940(%r3)
	lis %r11, -20904
	ori %r11, %r11, 25479
	stw %r11, 2944(%r3)
	lis %r11, -32748
	ori %r11, %r11, 25935
	stw %r11, 2948(%r3)
	lis %r11, -5579
	ori %r11, %r11, 43039
	stw %r11, 2952(%r3)
	lis %r11, 30967
	ori %r11, %r11, 41615
	stw %r11, 2956(%r3)
	lis %r11, -15330
	ori %r11, %r11, 38426
	stw %r11, 2960(%r3)
	lis %r11, -31846
	ori %r11, %r11, 47599
	stw %r11, 2964(%r3)
	lis %r11, 24221
	ori %r11, %r11, 55519
	stw %r11, 2968(%r3)
	lis %r11, -17013
	ori %r11, %r11, 10592
	stw %r11, 2972(%r3)
	lis %r11, -22282
	ori %r11, %r11, 16201
	stw %r11, 2976(%r3)
	lis %r11, -3925
	ori %r11, %r11, 3228
	stw %r11, 2980(%r3)
	lis %r11, -14137
	ori %r11, %r11, 30852
	stw %r11, 2984(%r3)
	lis %r11, -1572
	ori %r11, %r11, 23108
	stw %r11, 2988(%r3)
	lis %r11, 11724
	ori %r11, %r11, 55690
	stw %r11, 2992(%r3)
	lis %r11, 30545
	ori %r11, %r11, 27961
	stw %r11, 2996(%r3)
	lis %r11, -12197
	ori %r11, %r11, 17056
	stw %r11, 3000(%r3)
	lis %r11, 4041
	ori %r11, %r11, 19728
	stw %r11, 3004(%r3)
	lis %r11, 0
	ori %r11, %r11, 77
	stw %r11, 3008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3012(%r3)
	addi %r6, %r12, 1
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	addi %r6, %r6, 66
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2656(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2664(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2672(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2680(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2688(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2696(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2704(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2712(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2720(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2440(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2444(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2448(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2452(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2456(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2460(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2464(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2468(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2472(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2476(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2480(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2484(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2488(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2492(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2496(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2500(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2504(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2508(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2656(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2660(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2664(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2668(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2672(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2676(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2680(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2684(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2688(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2692(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2696(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2700(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2704(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2708(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2712(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2716(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2720(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2724(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	bl {vg_p521_validate}
	bl {vg_p521_windows}
	bl {vg_p521_inv_mod_p}
	li %r4, 2512
	li %r5, 1072
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2584
	li %r5, 2512
	li %r6, 352
	bl {vg_p521_mul_mod_p}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2368(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2372(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2376(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2380(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2384(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2388(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2392(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2396(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2400(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2404(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2408(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2412(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2416(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2420(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2424(%r3)
	lwz %r8, 192(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2428(%r3)
	lwz %r8, 196(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2432(%r3)
	lwz %r8, 200(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2436(%r3)
	lwz %r8, 204(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2368(%r3)
	ld %r4, 2376(%r3)
	or %r5, %r5, %r4
	ld %r4, 2384(%r3)
	or %r5, %r5, %r4
	ld %r4, 2392(%r3)
	or %r5, %r5, %r4
	ld %r4, 2400(%r3)
	or %r5, %r5, %r4
	ld %r4, 2408(%r3)
	or %r5, %r5, %r4
	ld %r4, 2416(%r3)
	or %r5, %r5, %r4
	ld %r4, 2424(%r3)
	or %r5, %r5, %r4
	ld %r4, 2432(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r5, 1216(%r3)
	ld %r4, 1224(%r3)
	or %r5, %r5, %r4
	ld %r4, 1232(%r3)
	or %r5, %r5, %r4
	ld %r4, 1240(%r3)
	or %r5, %r5, %r4
	ld %r4, 1248(%r3)
	or %r5, %r5, %r4
	ld %r4, 1256(%r3)
	or %r5, %r5, %r4
	ld %r4, 1264(%r3)
	or %r5, %r5, %r4
	ld %r4, 1272(%r3)
	or %r5, %r5, %r4
	ld %r4, 1280(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	ld %r4, 2584(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r14, %r6
	ld %r4, 2592(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r14, %r6
	ld %r4, 2600(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r14, %r6
	ld %r4, 2608(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r14, %r6
	ld %r4, 2616(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r14, %r6
	ld %r4, 2624(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r14, %r6
	ld %r4, 2632(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r14, %r6
	ld %r4, 2640(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r14, %r6
	ld %r4, 2648(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r14)
	stb %r4, 1(%r14)
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
