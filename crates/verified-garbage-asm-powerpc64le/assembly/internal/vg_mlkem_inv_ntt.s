// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	std %r14, 512(%r4)
	std %r15, 520(%r4)
	li %r12, 1
	stw %r12, 0(%r4)
	li %r12, 1729
	stw %r12, 4(%r4)
	li %r12, 2580
	stw %r12, 8(%r4)
	li %r12, 3289
	stw %r12, 12(%r4)
	li %r12, 2642
	stw %r12, 16(%r4)
	li %r12, 630
	stw %r12, 20(%r4)
	li %r12, 1897
	stw %r12, 24(%r4)
	li %r12, 848
	stw %r12, 28(%r4)
	li %r12, 1062
	stw %r12, 32(%r4)
	li %r12, 1919
	stw %r12, 36(%r4)
	li %r12, 193
	stw %r12, 40(%r4)
	li %r12, 797
	stw %r12, 44(%r4)
	li %r12, 2786
	stw %r12, 48(%r4)
	li %r12, 3260
	stw %r12, 52(%r4)
	li %r12, 569
	stw %r12, 56(%r4)
	li %r12, 1746
	stw %r12, 60(%r4)
	li %r12, 296
	stw %r12, 64(%r4)
	li %r12, 2447
	stw %r12, 68(%r4)
	li %r12, 1339
	stw %r12, 72(%r4)
	li %r12, 1476
	stw %r12, 76(%r4)
	li %r12, 3046
	stw %r12, 80(%r4)
	li %r12, 56
	stw %r12, 84(%r4)
	li %r12, 2240
	stw %r12, 88(%r4)
	li %r12, 1333
	stw %r12, 92(%r4)
	li %r12, 1426
	stw %r12, 96(%r4)
	li %r12, 2094
	stw %r12, 100(%r4)
	li %r12, 535
	stw %r12, 104(%r4)
	li %r12, 2882
	stw %r12, 108(%r4)
	li %r12, 2393
	stw %r12, 112(%r4)
	li %r12, 2879
	stw %r12, 116(%r4)
	li %r12, 1974
	stw %r12, 120(%r4)
	li %r12, 821
	stw %r12, 124(%r4)
	li %r12, 289
	stw %r12, 128(%r4)
	li %r12, 331
	stw %r12, 132(%r4)
	li %r12, 3253
	stw %r12, 136(%r4)
	li %r12, 1756
	stw %r12, 140(%r4)
	li %r12, 1197
	stw %r12, 144(%r4)
	li %r12, 2304
	stw %r12, 148(%r4)
	li %r12, 2277
	stw %r12, 152(%r4)
	li %r12, 2055
	stw %r12, 156(%r4)
	li %r12, 650
	stw %r12, 160(%r4)
	li %r12, 1977
	stw %r12, 164(%r4)
	li %r12, 2513
	stw %r12, 168(%r4)
	li %r12, 632
	stw %r12, 172(%r4)
	li %r12, 2865
	stw %r12, 176(%r4)
	li %r12, 33
	stw %r12, 180(%r4)
	li %r12, 1320
	stw %r12, 184(%r4)
	li %r12, 1915
	stw %r12, 188(%r4)
	li %r12, 2319
	stw %r12, 192(%r4)
	li %r12, 1435
	stw %r12, 196(%r4)
	li %r12, 807
	stw %r12, 200(%r4)
	li %r12, 452
	stw %r12, 204(%r4)
	li %r12, 1438
	stw %r12, 208(%r4)
	li %r12, 2868
	stw %r12, 212(%r4)
	li %r12, 1534
	stw %r12, 216(%r4)
	li %r12, 2402
	stw %r12, 220(%r4)
	li %r12, 2647
	stw %r12, 224(%r4)
	li %r12, 2617
	stw %r12, 228(%r4)
	li %r12, 1481
	stw %r12, 232(%r4)
	li %r12, 648
	stw %r12, 236(%r4)
	li %r12, 2474
	stw %r12, 240(%r4)
	li %r12, 3110
	stw %r12, 244(%r4)
	li %r12, 1227
	stw %r12, 248(%r4)
	li %r12, 910
	stw %r12, 252(%r4)
	li %r12, 17
	stw %r12, 256(%r4)
	li %r12, 2761
	stw %r12, 260(%r4)
	li %r12, 583
	stw %r12, 264(%r4)
	li %r12, 2649
	stw %r12, 268(%r4)
	li %r12, 1637
	stw %r12, 272(%r4)
	li %r12, 723
	stw %r12, 276(%r4)
	li %r12, 2288
	stw %r12, 280(%r4)
	li %r12, 1100
	stw %r12, 284(%r4)
	li %r12, 1409
	stw %r12, 288(%r4)
	li %r12, 2662
	stw %r12, 292(%r4)
	li %r12, 3281
	stw %r12, 296(%r4)
	li %r12, 233
	stw %r12, 300(%r4)
	li %r12, 756
	stw %r12, 304(%r4)
	li %r12, 2156
	stw %r12, 308(%r4)
	li %r12, 3015
	stw %r12, 312(%r4)
	li %r12, 3050
	stw %r12, 316(%r4)
	li %r12, 1703
	stw %r12, 320(%r4)
	li %r12, 1651
	stw %r12, 324(%r4)
	li %r12, 2789
	stw %r12, 328(%r4)
	li %r12, 1789
	stw %r12, 332(%r4)
	li %r12, 1847
	stw %r12, 336(%r4)
	li %r12, 952
	stw %r12, 340(%r4)
	li %r12, 1461
	stw %r12, 344(%r4)
	li %r12, 2687
	stw %r12, 348(%r4)
	li %r12, 939
	stw %r12, 352(%r4)
	li %r12, 2308
	stw %r12, 356(%r4)
	li %r12, 2437
	stw %r12, 360(%r4)
	li %r12, 2388
	stw %r12, 364(%r4)
	li %r12, 733
	stw %r12, 368(%r4)
	li %r12, 2337
	stw %r12, 372(%r4)
	li %r12, 268
	stw %r12, 376(%r4)
	li %r12, 641
	stw %r12, 380(%r4)
	li %r12, 1584
	stw %r12, 384(%r4)
	li %r12, 2298
	stw %r12, 388(%r4)
	li %r12, 2037
	stw %r12, 392(%r4)
	li %r12, 3220
	stw %r12, 396(%r4)
	li %r12, 375
	stw %r12, 400(%r4)
	li %r12, 2549
	stw %r12, 404(%r4)
	li %r12, 2090
	stw %r12, 408(%r4)
	li %r12, 1645
	stw %r12, 412(%r4)
	li %r12, 1063
	stw %r12, 416(%r4)
	li %r12, 319
	stw %r12, 420(%r4)
	li %r12, 2773
	stw %r12, 424(%r4)
	li %r12, 757
	stw %r12, 428(%r4)
	li %r12, 2099
	stw %r12, 432(%r4)
	li %r12, 561
	stw %r12, 436(%r4)
	li %r12, 2466
	stw %r12, 440(%r4)
	li %r12, 2594
	stw %r12, 444(%r4)
	li %r12, 2804
	stw %r12, 448(%r4)
	li %r12, 1092
	stw %r12, 452(%r4)
	li %r12, 403
	stw %r12, 456(%r4)
	li %r12, 1026
	stw %r12, 460(%r4)
	li %r12, 1143
	stw %r12, 464(%r4)
	li %r12, 2150
	stw %r12, 468(%r4)
	li %r12, 2775
	stw %r12, 472(%r4)
	li %r12, 886
	stw %r12, 476(%r4)
	li %r12, 1722
	stw %r12, 480(%r4)
	li %r12, 1212
	stw %r12, 484(%r4)
	li %r12, 1874
	stw %r12, 488(%r4)
	li %r12, 1029
	stw %r12, 492(%r4)
	li %r12, 2110
	stw %r12, 496(%r4)
	li %r12, 2935
	stw %r12, 500(%r4)
	li %r12, 885
	stw %r12, 504(%r4)
	li %r12, 2154
	stw %r12, 508(%r4)
	lis %r8, 2
	ori %r8, %r8, 30198
	li %r9, 3329
	addi %r3, %r3, 1024
	addi %r4, %r4, 508
	li %r10, 8
20:
	addi %r5, %r3, -1024
21:
	lwz %r7, 0(%r4)
	addi %r4, %r4, -4
	add %r6, %r5, %r10
	rldicl %r11, %r10, 62, 2
22:
	lwz %r12, 0(%r5)
	lwz %r0, 0(%r6)
	add %r14, %r12, %r0
	subf %r14, %r9, %r14
	rldicl %r15, %r14, 1, 63
	mulld %r15, %r15, %r9
	add %r14, %r14, %r15
	stw %r14, 0(%r5)
	subf %r0, %r12, %r0
	rldicl %r15, %r0, 1, 63
	mulld %r15, %r15, %r9
	add %r0, %r0, %r15
	mulld %r0, %r7, %r0
	rldicl %r14, %r0, 53, 11
	mulld %r14, %r14, %r8
	rldicl %r14, %r14, 46, 18
	mulld %r14, %r14, %r9
	subf %r0, %r14, %r0
	subf %r0, %r9, %r0
	rldicl %r14, %r0, 1, 63
	mulld %r14, %r14, %r9
	add %r0, %r0, %r14
	stw %r0, 0(%r6)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r5, %r6, 0
	subf %r0, %r3, %r5
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicr %r10, %r10, 1, 62
	addi %r0, %r10, -1024
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	li %r7, 3303
	addi %r5, %r3, -1024
	li %r11, 256
23:
	lwz %r12, 0(%r5)
	mulld %r12, %r12, %r7
	rldicl %r14, %r12, 53, 11
	mulld %r14, %r14, %r8
	rldicl %r14, %r14, 46, 18
	mulld %r14, %r14, %r9
	subf %r12, %r14, %r12
	subf %r12, %r9, %r12
	rldicl %r14, %r12, 1, 63
	mulld %r14, %r14, %r9
	add %r12, %r12, %r14
	stw %r12, 0(%r5)
	addi %r5, %r5, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	ld %r14, 512(%r4)
	ld %r15, 520(%r4)
	blr
