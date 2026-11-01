// The functions of `src/pbkdf2_sha384.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha384_iterate:
	mflr %r0
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	std %r26, 176(%r7)
	std %r27, 184(%r7)
	std %r28, 192(%r7)
	std %r29, 200(%r7)
	std %r30, 208(%r7)
	std %r31, 216(%r7)
	std %r0, 224(%r7)
	addi %r26, %r7, 232
	addi %r27, %r7, 0
	addi %r28, %r7, 296
	addi %r30, %r6, 0
	addi %r31, %r5, 0
	lwz %r8, 0(%r4)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r4)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r4)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r4)
	stw %r8, 12(%r28)
	lwz %r8, 16(%r4)
	stw %r8, 16(%r28)
	lwz %r8, 20(%r4)
	stw %r8, 20(%r28)
	lwz %r8, 24(%r4)
	stw %r8, 24(%r28)
	lwz %r8, 28(%r4)
	stw %r8, 28(%r28)
	lwz %r8, 32(%r4)
	stw %r8, 32(%r28)
	lwz %r8, 36(%r4)
	stw %r8, 36(%r28)
	lwz %r8, 40(%r4)
	stw %r8, 40(%r28)
	lwz %r8, 44(%r4)
	stw %r8, 44(%r28)
	li %r8, 128
	stw %r8, 48(%r28)
	li %r8, 0
	stw %r8, 52(%r28)
	stw %r8, 56(%r28)
	stw %r8, 60(%r28)
	stw %r8, 64(%r28)
	stw %r8, 68(%r28)
	stw %r8, 72(%r28)
	stw %r8, 76(%r28)
	stw %r8, 80(%r28)
	stw %r8, 84(%r28)
	stw %r8, 88(%r28)
	stw %r8, 92(%r28)
	stw %r8, 96(%r28)
	stw %r8, 100(%r28)
	stw %r8, 104(%r28)
	stw %r8, 108(%r28)
	li %r29, 176
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r29, %r3, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 4(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 8(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 12(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 16(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 20(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 24(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 28(%r29)
	stw %r8, 28(%r26)
	lwz %r8, 32(%r29)
	stw %r8, 32(%r26)
	lwz %r8, 36(%r29)
	stw %r8, 36(%r26)
	lwz %r8, 40(%r29)
	stw %r8, 40(%r26)
	lwz %r8, 44(%r29)
	stw %r8, 44(%r26)
	lwz %r8, 48(%r29)
	stw %r8, 48(%r26)
	lwz %r8, 52(%r29)
	stw %r8, 52(%r26)
	lwz %r8, 56(%r29)
	stw %r8, 56(%r26)
	lwz %r8, 60(%r29)
	stw %r8, 60(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha512_compress}
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	lwz %r8, 192(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 196(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 200(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 204(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 208(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 212(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 216(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 220(%r29)
	stw %r8, 28(%r26)
	lwz %r8, 224(%r29)
	stw %r8, 32(%r26)
	lwz %r8, 228(%r29)
	stw %r8, 36(%r26)
	lwz %r8, 232(%r29)
	stw %r8, 40(%r26)
	lwz %r8, 236(%r29)
	stw %r8, 44(%r26)
	lwz %r8, 240(%r29)
	stw %r8, 48(%r26)
	lwz %r8, 244(%r29)
	stw %r8, 52(%r26)
	lwz %r8, 248(%r29)
	stw %r8, 56(%r26)
	lwz %r8, 252(%r29)
	stw %r8, 60(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha512_compress}
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	lwz %r8, 0(%r28)
	lwz %r9, 0(%r30)
	xor %r8, %r8, %r9
	stw %r8, 0(%r30)
	lwz %r8, 4(%r28)
	lwz %r9, 4(%r30)
	xor %r8, %r8, %r9
	stw %r8, 4(%r30)
	lwz %r8, 8(%r28)
	lwz %r9, 8(%r30)
	xor %r8, %r8, %r9
	stw %r8, 8(%r30)
	lwz %r8, 12(%r28)
	lwz %r9, 12(%r30)
	xor %r8, %r8, %r9
	stw %r8, 12(%r30)
	lwz %r8, 16(%r28)
	lwz %r9, 16(%r30)
	xor %r8, %r8, %r9
	stw %r8, 16(%r30)
	lwz %r8, 20(%r28)
	lwz %r9, 20(%r30)
	xor %r8, %r8, %r9
	stw %r8, 20(%r30)
	lwz %r8, 24(%r28)
	lwz %r9, 24(%r30)
	xor %r8, %r8, %r9
	stw %r8, 24(%r30)
	lwz %r8, 28(%r28)
	lwz %r9, 28(%r30)
	xor %r8, %r8, %r9
	stw %r8, 28(%r30)
	lwz %r8, 32(%r28)
	lwz %r9, 32(%r30)
	xor %r8, %r8, %r9
	stw %r8, 32(%r30)
	lwz %r8, 36(%r28)
	lwz %r9, 36(%r30)
	xor %r8, %r8, %r9
	stw %r8, 36(%r30)
	lwz %r8, 40(%r28)
	lwz %r9, 40(%r30)
	xor %r8, %r8, %r9
	stw %r8, 40(%r30)
	lwz %r8, 44(%r28)
	lwz %r9, 44(%r30)
	xor %r8, %r8, %r9
	stw %r8, 44(%r30)
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 224(%r27)
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	mtlr %r0
	blr

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
