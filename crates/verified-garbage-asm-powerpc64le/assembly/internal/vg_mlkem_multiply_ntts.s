// The functions of `src/internal/vg_mlkem_multiply_ntts.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_multiply_ntts:
	std %r14, 512(%r6)
	std %r15, 520(%r6)
	li %r12, 17
	stw %r12, 0(%r6)
	li %r12, 3312
	stw %r12, 4(%r6)
	li %r12, 2761
	stw %r12, 8(%r6)
	li %r12, 568
	stw %r12, 12(%r6)
	li %r12, 583
	stw %r12, 16(%r6)
	li %r12, 2746
	stw %r12, 20(%r6)
	li %r12, 2649
	stw %r12, 24(%r6)
	li %r12, 680
	stw %r12, 28(%r6)
	li %r12, 1637
	stw %r12, 32(%r6)
	li %r12, 1692
	stw %r12, 36(%r6)
	li %r12, 723
	stw %r12, 40(%r6)
	li %r12, 2606
	stw %r12, 44(%r6)
	li %r12, 2288
	stw %r12, 48(%r6)
	li %r12, 1041
	stw %r12, 52(%r6)
	li %r12, 1100
	stw %r12, 56(%r6)
	li %r12, 2229
	stw %r12, 60(%r6)
	li %r12, 1409
	stw %r12, 64(%r6)
	li %r12, 1920
	stw %r12, 68(%r6)
	li %r12, 2662
	stw %r12, 72(%r6)
	li %r12, 667
	stw %r12, 76(%r6)
	li %r12, 3281
	stw %r12, 80(%r6)
	li %r12, 48
	stw %r12, 84(%r6)
	li %r12, 233
	stw %r12, 88(%r6)
	li %r12, 3096
	stw %r12, 92(%r6)
	li %r12, 756
	stw %r12, 96(%r6)
	li %r12, 2573
	stw %r12, 100(%r6)
	li %r12, 2156
	stw %r12, 104(%r6)
	li %r12, 1173
	stw %r12, 108(%r6)
	li %r12, 3015
	stw %r12, 112(%r6)
	li %r12, 314
	stw %r12, 116(%r6)
	li %r12, 3050
	stw %r12, 120(%r6)
	li %r12, 279
	stw %r12, 124(%r6)
	li %r12, 1703
	stw %r12, 128(%r6)
	li %r12, 1626
	stw %r12, 132(%r6)
	li %r12, 1651
	stw %r12, 136(%r6)
	li %r12, 1678
	stw %r12, 140(%r6)
	li %r12, 2789
	stw %r12, 144(%r6)
	li %r12, 540
	stw %r12, 148(%r6)
	li %r12, 1789
	stw %r12, 152(%r6)
	li %r12, 1540
	stw %r12, 156(%r6)
	li %r12, 1847
	stw %r12, 160(%r6)
	li %r12, 1482
	stw %r12, 164(%r6)
	li %r12, 952
	stw %r12, 168(%r6)
	li %r12, 2377
	stw %r12, 172(%r6)
	li %r12, 1461
	stw %r12, 176(%r6)
	li %r12, 1868
	stw %r12, 180(%r6)
	li %r12, 2687
	stw %r12, 184(%r6)
	li %r12, 642
	stw %r12, 188(%r6)
	li %r12, 939
	stw %r12, 192(%r6)
	li %r12, 2390
	stw %r12, 196(%r6)
	li %r12, 2308
	stw %r12, 200(%r6)
	li %r12, 1021
	stw %r12, 204(%r6)
	li %r12, 2437
	stw %r12, 208(%r6)
	li %r12, 892
	stw %r12, 212(%r6)
	li %r12, 2388
	stw %r12, 216(%r6)
	li %r12, 941
	stw %r12, 220(%r6)
	li %r12, 733
	stw %r12, 224(%r6)
	li %r12, 2596
	stw %r12, 228(%r6)
	li %r12, 2337
	stw %r12, 232(%r6)
	li %r12, 992
	stw %r12, 236(%r6)
	li %r12, 268
	stw %r12, 240(%r6)
	li %r12, 3061
	stw %r12, 244(%r6)
	li %r12, 641
	stw %r12, 248(%r6)
	li %r12, 2688
	stw %r12, 252(%r6)
	li %r12, 1584
	stw %r12, 256(%r6)
	li %r12, 1745
	stw %r12, 260(%r6)
	li %r12, 2298
	stw %r12, 264(%r6)
	li %r12, 1031
	stw %r12, 268(%r6)
	li %r12, 2037
	stw %r12, 272(%r6)
	li %r12, 1292
	stw %r12, 276(%r6)
	li %r12, 3220
	stw %r12, 280(%r6)
	li %r12, 109
	stw %r12, 284(%r6)
	li %r12, 375
	stw %r12, 288(%r6)
	li %r12, 2954
	stw %r12, 292(%r6)
	li %r12, 2549
	stw %r12, 296(%r6)
	li %r12, 780
	stw %r12, 300(%r6)
	li %r12, 2090
	stw %r12, 304(%r6)
	li %r12, 1239
	stw %r12, 308(%r6)
	li %r12, 1645
	stw %r12, 312(%r6)
	li %r12, 1684
	stw %r12, 316(%r6)
	li %r12, 1063
	stw %r12, 320(%r6)
	li %r12, 2266
	stw %r12, 324(%r6)
	li %r12, 319
	stw %r12, 328(%r6)
	li %r12, 3010
	stw %r12, 332(%r6)
	li %r12, 2773
	stw %r12, 336(%r6)
	li %r12, 556
	stw %r12, 340(%r6)
	li %r12, 757
	stw %r12, 344(%r6)
	li %r12, 2572
	stw %r12, 348(%r6)
	li %r12, 2099
	stw %r12, 352(%r6)
	li %r12, 1230
	stw %r12, 356(%r6)
	li %r12, 561
	stw %r12, 360(%r6)
	li %r12, 2768
	stw %r12, 364(%r6)
	li %r12, 2466
	stw %r12, 368(%r6)
	li %r12, 863
	stw %r12, 372(%r6)
	li %r12, 2594
	stw %r12, 376(%r6)
	li %r12, 735
	stw %r12, 380(%r6)
	li %r12, 2804
	stw %r12, 384(%r6)
	li %r12, 525
	stw %r12, 388(%r6)
	li %r12, 1092
	stw %r12, 392(%r6)
	li %r12, 2237
	stw %r12, 396(%r6)
	li %r12, 403
	stw %r12, 400(%r6)
	li %r12, 2926
	stw %r12, 404(%r6)
	li %r12, 1026
	stw %r12, 408(%r6)
	li %r12, 2303
	stw %r12, 412(%r6)
	li %r12, 1143
	stw %r12, 416(%r6)
	li %r12, 2186
	stw %r12, 420(%r6)
	li %r12, 2150
	stw %r12, 424(%r6)
	li %r12, 1179
	stw %r12, 428(%r6)
	li %r12, 2775
	stw %r12, 432(%r6)
	li %r12, 554
	stw %r12, 436(%r6)
	li %r12, 886
	stw %r12, 440(%r6)
	li %r12, 2443
	stw %r12, 444(%r6)
	li %r12, 1722
	stw %r12, 448(%r6)
	li %r12, 1607
	stw %r12, 452(%r6)
	li %r12, 1212
	stw %r12, 456(%r6)
	li %r12, 2117
	stw %r12, 460(%r6)
	li %r12, 1874
	stw %r12, 464(%r6)
	li %r12, 1455
	stw %r12, 468(%r6)
	li %r12, 1029
	stw %r12, 472(%r6)
	li %r12, 2300
	stw %r12, 476(%r6)
	li %r12, 2110
	stw %r12, 480(%r6)
	li %r12, 1219
	stw %r12, 484(%r6)
	li %r12, 2935
	stw %r12, 488(%r6)
	li %r12, 394
	stw %r12, 492(%r6)
	li %r12, 885
	stw %r12, 496(%r6)
	li %r12, 2444
	stw %r12, 500(%r6)
	li %r12, 2154
	stw %r12, 504(%r6)
	li %r12, 1175
	stw %r12, 508(%r6)
	lis %r8, 2
	ori %r8, %r8, 30198
	li %r9, 3329
	li %r11, 128
20:
	lwz %r7, 0(%r4)
	lwz %r12, 4(%r4)
	lwz %r14, 0(%r5)
	lwz %r15, 4(%r5)
	mulld %r0, %r12, %r15
	rldicl %r10, %r0, 53, 11
	mulld %r10, %r10, %r8
	rldicl %r10, %r10, 46, 18
	mulld %r10, %r10, %r9
	subf %r0, %r10, %r0
	subf %r0, %r9, %r0
	rldicl %r10, %r0, 1, 63
	mulld %r10, %r10, %r9
	add %r0, %r0, %r10
	lwz %r10, 0(%r6)
	mulld %r0, %r0, %r10
	mulld %r10, %r7, %r14
	add %r0, %r10, %r0
	rldicl %r10, %r0, 53, 11
	mulld %r10, %r10, %r8
	rldicl %r10, %r10, 46, 18
	mulld %r10, %r10, %r9
	subf %r0, %r10, %r0
	subf %r0, %r9, %r0
	rldicl %r10, %r0, 1, 63
	mulld %r10, %r10, %r9
	add %r0, %r0, %r10
	stw %r0, 0(%r3)
	mulld %r0, %r7, %r15
	mulld %r10, %r12, %r14
	add %r0, %r0, %r10
	rldicl %r10, %r0, 53, 11
	mulld %r10, %r10, %r8
	rldicl %r10, %r10, 46, 18
	mulld %r10, %r10, %r9
	subf %r0, %r10, %r0
	subf %r0, %r9, %r0
	rldicl %r10, %r0, 1, 63
	mulld %r10, %r10, %r9
	add %r0, %r0, %r10
	stw %r0, 4(%r3)
	addi %r3, %r3, 8
	addi %r4, %r4, 8
	addi %r5, %r5, 8
	addi %r6, %r6, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	blr
