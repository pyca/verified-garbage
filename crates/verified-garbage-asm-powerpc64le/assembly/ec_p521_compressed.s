// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P521_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P521_FRAME_CONSTS}
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
	ld %r11, 64(%r4)
	std %r11, 128(%r9)
	addi %r4, %r4, 72
	addi %r9, %r9, 72
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 3232(%r3)
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
	ld %r10, 3232(%r3)
	ld %r4, 2656(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2440(%r3)
	and %r4, %r4, %r10
	li %r6, 59
	stdbrx %r4, %r14, %r6
	ld %r4, 2448(%r3)
	and %r4, %r4, %r10
	li %r6, 51
	stdbrx %r4, %r14, %r6
	ld %r4, 2456(%r3)
	and %r4, %r4, %r10
	li %r6, 43
	stdbrx %r4, %r14, %r6
	ld %r4, 2464(%r3)
	and %r4, %r4, %r10
	li %r6, 35
	stdbrx %r4, %r14, %r6
	ld %r4, 2472(%r3)
	and %r4, %r4, %r10
	li %r6, 27
	stdbrx %r4, %r14, %r6
	ld %r4, 2480(%r3)
	and %r4, %r4, %r10
	li %r6, 19
	stdbrx %r4, %r14, %r6
	ld %r4, 2488(%r3)
	and %r4, %r4, %r10
	li %r6, 11
	stdbrx %r4, %r14, %r6
	ld %r4, 2496(%r3)
	and %r4, %r4, %r10
	li %r6, 3
	stdbrx %r4, %r14, %r6
	ld %r4, 2504(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 1(%r14)
	stb %r4, 2(%r14)
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

vg_ec_p521_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P521_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P521_FRAME_CONSTS}
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
	ld %r11, 64(%r4)
	std %r11, 128(%r9)
	addi %r4, %r4, 72
	addi %r9, %r9, 72
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 3232(%r3)
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
	lbz %r4, 0(%r12)
	std %r4, 2368(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
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
	li %r4, 2512
	li %r5, 2440
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2512
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3088
	li %r5, 3016
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 496
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3088
	li %r6, 3016
	bl {vg_p521_add_mod_p}
	li %r4, 3088
	li %r5, 2800
	li %r6, 2944
	bl {vg_p521_add_mod_p}
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 940(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 944(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 952(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 956(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 960(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 964(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 968(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 972(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 976(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 980(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 984(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 988(%r3)
	lis %r11, 0
	ori %r11, %r11, 128
	stw %r11, 992(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 996(%r3)
	li %r31, 72
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 928(%r4)
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
	bne %cr0, 21b
	ld %r4, 424(%r3)
	std %r4, 2152(%r3)
	ld %r4, 432(%r3)
	std %r4, 2160(%r3)
	ld %r4, 440(%r3)
	std %r4, 2168(%r3)
	ld %r4, 448(%r3)
	std %r4, 2176(%r3)
	ld %r4, 456(%r3)
	std %r4, 2184(%r3)
	ld %r4, 464(%r3)
	std %r4, 2192(%r3)
	ld %r4, 472(%r3)
	std %r4, 2200(%r3)
	ld %r4, 480(%r3)
	std %r4, 2208(%r3)
	ld %r4, 488(%r3)
	std %r4, 2216(%r3)
	li %r31, 576
22:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2224
	li %r5, 2152
	li %r6, 3088
	bl {vg_p521_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 5248(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 2152(%r3)
	ld %r5, 2224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2152(%r3)
	ld %r4, 2160(%r3)
	ld %r5, 2232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2160(%r3)
	ld %r4, 2168(%r3)
	ld %r5, 2240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2168(%r3)
	ld %r4, 2176(%r3)
	ld %r5, 2248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r4, 2184(%r3)
	ld %r5, 2256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2184(%r3)
	ld %r4, 2192(%r3)
	ld %r5, 2264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2192(%r3)
	ld %r4, 2200(%r3)
	ld %r5, 2272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2200(%r3)
	ld %r4, 2208(%r3)
	ld %r5, 2280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2208(%r3)
	ld %r4, 2216(%r3)
	ld %r5, 2288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2216(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 2656
	li %r5, 2152
	li %r6, 352
	bl {vg_p521_mul_mod_p}
	li %r4, 2728
	li %r5, 280
	li %r6, 2656
	bl {vg_p521_sub_mod_p}
	ld %r4, 2656(%r3)
	ld %r5, 2368(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 2656(%r3)
	ld %r5, 2728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2656(%r3)
	ld %r4, 2664(%r3)
	ld %r5, 2736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2664(%r3)
	ld %r4, 2672(%r3)
	ld %r5, 2744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2672(%r3)
	ld %r4, 2680(%r3)
	ld %r5, 2752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2680(%r3)
	ld %r4, 2688(%r3)
	ld %r5, 2760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2688(%r3)
	ld %r4, 2696(%r3)
	ld %r5, 2768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2696(%r3)
	ld %r4, 2704(%r3)
	ld %r5, 2776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2704(%r3)
	ld %r4, 2712(%r3)
	ld %r5, 2784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2712(%r3)
	ld %r4, 2720(%r3)
	ld %r5, 2792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2720(%r3)
	li %r4, 2584
	li %r5, 2656
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2584
	li %r6, 2584
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3016
	li %r6, 3088
	bl {vg_p521_sub_mod_p}
	ld %r5, 2800(%r3)
	ld %r4, 2808(%r3)
	or %r5, %r5, %r4
	ld %r4, 2816(%r3)
	or %r5, %r5, %r4
	ld %r4, 2824(%r3)
	or %r5, %r5, %r4
	ld %r4, 2832(%r3)
	or %r5, %r5, %r4
	ld %r4, 2840(%r3)
	or %r5, %r5, %r4
	ld %r4, 2848(%r3)
	or %r5, %r5, %r4
	ld %r4, 2856(%r3)
	or %r5, %r5, %r4
	ld %r4, 2864(%r3)
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
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r4, 2656(%r3)
	ld %r5, 2368(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2440(%r3)
	and %r4, %r4, %r10
	li %r6, 59
	stdbrx %r4, %r14, %r6
	ld %r4, 2448(%r3)
	and %r4, %r4, %r10
	li %r6, 51
	stdbrx %r4, %r14, %r6
	ld %r4, 2456(%r3)
	and %r4, %r4, %r10
	li %r6, 43
	stdbrx %r4, %r14, %r6
	ld %r4, 2464(%r3)
	and %r4, %r4, %r10
	li %r6, 35
	stdbrx %r4, %r14, %r6
	ld %r4, 2472(%r3)
	and %r4, %r4, %r10
	li %r6, 27
	stdbrx %r4, %r14, %r6
	ld %r4, 2480(%r3)
	and %r4, %r4, %r10
	li %r6, 19
	stdbrx %r4, %r14, %r6
	ld %r4, 2488(%r3)
	and %r4, %r4, %r10
	li %r6, 11
	stdbrx %r4, %r14, %r6
	ld %r4, 2496(%r3)
	and %r4, %r4, %r10
	li %r6, 3
	stdbrx %r4, %r14, %r6
	ld %r4, 2504(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 1(%r14)
	stb %r4, 2(%r14)
	ld %r4, 2656(%r3)
	and %r4, %r4, %r10
	li %r6, 125
	stdbrx %r4, %r14, %r6
	ld %r4, 2664(%r3)
	and %r4, %r4, %r10
	li %r6, 117
	stdbrx %r4, %r14, %r6
	ld %r4, 2672(%r3)
	and %r4, %r4, %r10
	li %r6, 109
	stdbrx %r4, %r14, %r6
	ld %r4, 2680(%r3)
	and %r4, %r4, %r10
	li %r6, 101
	stdbrx %r4, %r14, %r6
	ld %r4, 2688(%r3)
	and %r4, %r4, %r10
	li %r6, 93
	stdbrx %r4, %r14, %r6
	ld %r4, 2696(%r3)
	and %r4, %r4, %r10
	li %r6, 85
	stdbrx %r4, %r14, %r6
	ld %r4, 2704(%r3)
	and %r4, %r4, %r10
	li %r6, 77
	stdbrx %r4, %r14, %r6
	ld %r4, 2712(%r3)
	and %r4, %r4, %r10
	li %r6, 69
	stdbrx %r4, %r14, %r6
	ld %r4, 2720(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 67(%r14)
	stb %r4, 68(%r14)
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
