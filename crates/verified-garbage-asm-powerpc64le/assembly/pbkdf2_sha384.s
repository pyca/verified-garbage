// The functions of `src/pbkdf2_sha384.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha384:
	stdu %r1, -3440(%r1)
	addi %r10, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 0(%r10)
	std %r21, 8(%r10)
	std %r22, 16(%r10)
	std %r23, 24(%r10)
	std %r24, 32(%r10)
	std %r25, 40(%r10)
	addi %r21, %r10, 0
	addi %r20, %r6, 0
	addi %r22, %r7, 0
	addi %r23, %r8, 0
	addi %r24, %r9, 0
	addi %r25, %r5, 0
	addi %r5, %r3, 0
	addi %r6, %r4, 0
	addi %r3, %r21, 1920
	addi %r4, %r21, 2112
	bl {vg_hmac_sha384_init}
	li %r12, 1
	li %r11, 2592
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 1920(%r21)
	stw %r8, 2304(%r21)
	lwz %r8, 1924(%r21)
	stw %r8, 2308(%r21)
	lwz %r8, 1928(%r21)
	stw %r8, 2312(%r21)
	lwz %r8, 1932(%r21)
	stw %r8, 2316(%r21)
	lwz %r8, 1936(%r21)
	stw %r8, 2320(%r21)
	lwz %r8, 1940(%r21)
	stw %r8, 2324(%r21)
	lwz %r8, 1944(%r21)
	stw %r8, 2328(%r21)
	lwz %r8, 1948(%r21)
	stw %r8, 2332(%r21)
	lwz %r8, 1952(%r21)
	stw %r8, 2336(%r21)
	lwz %r8, 1956(%r21)
	stw %r8, 2340(%r21)
	lwz %r8, 1960(%r21)
	stw %r8, 2344(%r21)
	lwz %r8, 1964(%r21)
	stw %r8, 2348(%r21)
	lwz %r8, 1968(%r21)
	stw %r8, 2352(%r21)
	lwz %r8, 1972(%r21)
	stw %r8, 2356(%r21)
	lwz %r8, 1976(%r21)
	stw %r8, 2360(%r21)
	lwz %r8, 1980(%r21)
	stw %r8, 2364(%r21)
	lwz %r8, 1984(%r21)
	stw %r8, 2368(%r21)
	lwz %r8, 1988(%r21)
	stw %r8, 2372(%r21)
	lwz %r8, 1992(%r21)
	stw %r8, 2376(%r21)
	lwz %r8, 1996(%r21)
	stw %r8, 2380(%r21)
	lwz %r8, 2000(%r21)
	stw %r8, 2384(%r21)
	lwz %r8, 2004(%r21)
	stw %r8, 2388(%r21)
	lwz %r8, 2008(%r21)
	stw %r8, 2392(%r21)
	lwz %r8, 2012(%r21)
	stw %r8, 2396(%r21)
	lwz %r8, 2016(%r21)
	stw %r8, 2400(%r21)
	lwz %r8, 2020(%r21)
	stw %r8, 2404(%r21)
	lwz %r8, 2024(%r21)
	stw %r8, 2408(%r21)
	lwz %r8, 2028(%r21)
	stw %r8, 2412(%r21)
	lwz %r8, 2032(%r21)
	stw %r8, 2416(%r21)
	lwz %r8, 2036(%r21)
	stw %r8, 2420(%r21)
	lwz %r8, 2040(%r21)
	stw %r8, 2424(%r21)
	lwz %r8, 2044(%r21)
	stw %r8, 2428(%r21)
	lwz %r8, 2048(%r21)
	stw %r8, 2432(%r21)
	lwz %r8, 2052(%r21)
	stw %r8, 2436(%r21)
	lwz %r8, 2056(%r21)
	stw %r8, 2440(%r21)
	lwz %r8, 2060(%r21)
	stw %r8, 2444(%r21)
	lwz %r8, 2064(%r21)
	stw %r8, 2448(%r21)
	lwz %r8, 2068(%r21)
	stw %r8, 2452(%r21)
	lwz %r8, 2072(%r21)
	stw %r8, 2456(%r21)
	lwz %r8, 2076(%r21)
	stw %r8, 2460(%r21)
	lwz %r8, 2080(%r21)
	stw %r8, 2464(%r21)
	lwz %r8, 2084(%r21)
	stw %r8, 2468(%r21)
	lwz %r8, 2088(%r21)
	stw %r8, 2472(%r21)
	lwz %r8, 2092(%r21)
	stw %r8, 2476(%r21)
	lwz %r8, 2096(%r21)
	stw %r8, 2480(%r21)
	lwz %r8, 2100(%r21)
	stw %r8, 2484(%r21)
	lwz %r8, 2104(%r21)
	stw %r8, 2488(%r21)
	lwz %r8, 2108(%r21)
	stw %r8, 2492(%r21)
	addi %r3, %r21, 2304
	li %r4, 128
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_sha512_update_scratch}
	addi %r3, %r21, 2304
	addi %r4, %r20, 128
	addi %r5, %r21, 2592
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_sha512_update_scratch}
	addi %r3, %r21, 2304
	addi %r4, %r21, 2112
	addi %r5, %r20, 132
	addi %r6, %r21, 2496
	addi %r7, %r21, 48
	bl {vg_hmac_sha384_finalize_scratch}
	lwz %r8, 2496(%r21)
	stw %r8, 2544(%r21)
	lwz %r8, 2500(%r21)
	stw %r8, 2548(%r21)
	lwz %r8, 2504(%r21)
	stw %r8, 2552(%r21)
	lwz %r8, 2508(%r21)
	stw %r8, 2556(%r21)
	lwz %r8, 2512(%r21)
	stw %r8, 2560(%r21)
	lwz %r8, 2516(%r21)
	stw %r8, 2564(%r21)
	lwz %r8, 2520(%r21)
	stw %r8, 2568(%r21)
	lwz %r8, 2524(%r21)
	stw %r8, 2572(%r21)
	lwz %r8, 2528(%r21)
	stw %r8, 2576(%r21)
	lwz %r8, 2532(%r21)
	stw %r8, 2580(%r21)
	lwz %r8, 2536(%r21)
	stw %r8, 2584(%r21)
	lwz %r8, 2540(%r21)
	stw %r8, 2588(%r21)
	addi %r3, %r21, 1920
	addi %r4, %r21, 2496
	addi %r5, %r22, -1
	addi %r6, %r21, 2544
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_sha384_iterate}
	addi %r12, %r24, -48
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 48
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 2544(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 2592
	lwbrx %r12, %r21, %r11
	addi %r12, %r12, 1
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r20, 0(%r21)
	ld %r22, 16(%r21)
	ld %r23, 24(%r21)
	ld %r24, 32(%r21)
	ld %r25, 40(%r21)
	ld %r21, 8(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 3440
	blr
