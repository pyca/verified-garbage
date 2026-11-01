// The functions of `src/mlkem.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	mflr %r0
	std %r29, 1680(%r5)
	std %r30, 1688(%r5)
	std %r31, 1696(%r5)
	std %r0, 1704(%r5)
	addi %r29, %r3, 0
	addi %r30, %r4, 0
	addi %r31, %r5, 0
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 168
	li %r5, 0
	addi %r6, %r29, 0
	li %r7, 34
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 168
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 168
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 840
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 280
20:
	lbz %r7, 0(%r3)
	lbz %r8, 1(%r3)
	lbz %r9, 2(%r3)
	rldicr %r10, %r8, 60, 3
	rldicl %r10, %r10, 12, 52
	add %r10, %r7, %r10
	rldicl %r11, %r8, 60, 4
	rldicr %r12, %r9, 4, 59
	add %r11, %r11, %r12
	addi %r12, %r10, -3329
	rldicl %r12, %r12, 1, 63
	addi %r7, %r5, -256
	rldicl %r7, %r7, 1, 63
	and %r12, %r12, %r7
	cmpldi %cr0, %r12, 0
	beq %cr0, 21f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 22f
21:
22:
	addi %r12, %r11, -3329
	rldicl %r12, %r12, 1, 63
	addi %r7, %r5, -256
	rldicl %r7, %r7, 1, 63
	and %r12, %r12, %r7
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	stw %r11, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 24f
23:
24:
	addi %r3, %r3, 3
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	rldicl %r3, %r5, 56, 8
	ld %r0, 1704(%r31)
	mtlr %r0
	ld %r29, 1680(%r31)
	ld %r30, 1688(%r31)
	ld %r31, 1696(%r31)
	blr

vg_mlkem_ntt:
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
	addi %r4, %r4, 4
	li %r10, 512
20:
	addi %r5, %r3, -1024
21:
	lwz %r7, 0(%r4)
	addi %r4, %r4, 4
	add %r6, %r5, %r10
	rldicl %r11, %r10, 62, 2
22:
	lwz %r12, 0(%r5)
	lwz %r0, 0(%r6)
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
	subf %r14, %r0, %r12
	rldicl %r15, %r14, 1, 63
	mulld %r15, %r15, %r9
	add %r14, %r14, %r15
	stw %r14, 0(%r6)
	add %r12, %r12, %r0
	subf %r12, %r9, %r12
	rldicl %r15, %r12, 1, 63
	mulld %r15, %r15, %r9
	add %r12, %r12, %r15
	stw %r12, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r5, %r6, 0
	subf %r0, %r3, %r5
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicl %r10, %r10, 63, 1
	addi %r0, %r10, -4
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	ld %r14, 0(%r4)
	ld %r15, 8(%r4)
	blr

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

vg_mlkem_add:
	li %r5, 256
	li %r8, 3329
20:
	lwz %r6, 0(%r3)
	lwz %r7, 0(%r4)
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mlkem_sub:
	li %r5, 256
	li %r8, 3329
20:
	lwz %r6, 0(%r3)
	lwz %r7, 0(%r4)
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mlkem_cbd2:
	li %r5, 128
	li %r8, 3329
20:
	lbz %r6, 0(%r3)
	rldicr %r6, %r6, 62, 1
	rldicl %r6, %r6, 2, 62
	rldicl %r9, %r6, 63, 1
	subf %r6, %r9, %r6
	lbz %r7, 0(%r3)
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 2, 62
	rldicl %r9, %r7, 63, 1
	subf %r7, %r9, %r7
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r4)
	lbz %r6, 0(%r3)
	rldicr %r6, %r6, 58, 5
	rldicl %r6, %r6, 2, 62
	rldicl %r9, %r6, 63, 1
	subf %r6, %r9, %r6
	lbz %r7, 0(%r3)
	rldicr %r7, %r7, 56, 7
	rldicl %r7, %r7, 2, 62
	rldicl %r9, %r7, 63, 1
	subf %r7, %r9, %r7
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 4(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mlkem_encode12:
	li %r5, 128
20:
	lwz %r6, 0(%r3)
	lwz %r7, 4(%r3)
	stb %r6, 0(%r4)
	rldicl %r6, %r6, 56, 8
	rldicr %r8, %r7, 4, 59
	add %r6, %r6, %r8
	stb %r6, 1(%r4)
	rldicl %r7, %r7, 60, 4
	stb %r7, 2(%r4)
	addi %r3, %r3, 8
	addi %r4, %r4, 3
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mlkem_decode12:
	li %r5, 128
	li %r8, 3329
20:
	lbz %r6, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 12, 52
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r4)
	lbz %r6, 1(%r3)
	rldicl %r6, %r6, 60, 4
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 4, 59
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 4(%r4)
	addi %r3, %r3, 3
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mlkem_compress_encode:
	rlwinm %r4, %r4, 0, 0, 31
	addi %r7, %r4, -1
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	addi %r7, %r4, -4
	cmplwi %cr0, %r7, 0
	beq %cr0, 22f
	lis %r10, 3
	ori %r10, %r10, 65472
	lis %r9, 2
	ori %r9, %r9, 30199
	li %r11, 64
24:
	li %r8, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 10, 54
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 20, 44
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 30, 34
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 54, 9
	rldicl %r7, %r7, 40, 24
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	rldicl %r7, %r8, 56, 8
	stb %r7, 1(%r5)
	rldicl %r7, %r8, 48, 16
	stb %r7, 2(%r5)
	rldicl %r7, %r8, 40, 24
	stb %r7, 3(%r5)
	rldicl %r7, %r8, 32, 32
	stb %r7, 4(%r5)
	addi %r3, %r3, 16
	addi %r5, %r5, 5
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
	lis %r10, 3
	ori %r10, %r10, 65472
	li %r9, 2520
	li %r11, 128
25:
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 60, 3
	rldicl %r8, %r7, 4, 60
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 8, 56
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r3, %r3, 8
	addi %r5, %r5, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
23:
	b 21f
20:
	lis %r10, 3
	ori %r10, %r10, 65472
	li %r9, 315
	li %r11, 32
26:
	li %r8, 0
	lwz %r7, 0(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	add %r8, %r8, %r7
	lwz %r7, 4(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 2, 62
	add %r8, %r8, %r7
	lwz %r7, 8(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 3, 61
	add %r8, %r8, %r7
	lwz %r7, 12(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 4, 60
	add %r8, %r8, %r7
	lwz %r7, 16(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 5, 59
	add %r8, %r8, %r7
	lwz %r7, 20(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 6, 58
	add %r8, %r8, %r7
	lwz %r7, 24(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 7, 57
	add %r8, %r8, %r7
	lwz %r7, 28(%r3)
	mulld %r7, %r7, %r9
	add %r7, %r7, %r10
	rldicl %r7, %r7, 45, 19
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 8, 56
	add %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r3, %r3, 32
	addi %r5, %r5, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
21:
	blr

vg_mlkem_decode_decompress:
	rlwinm %r5, %r5, 0, 0, 31
	li %r9, 3329
	addi %r7, %r5, -1
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	addi %r7, %r5, -4
	cmplwi %cr0, %r7, 0
	beq %cr0, 22f
	li %r11, 64
24:
	lbz %r8, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 8, 55
	add %r8, %r8, %r7
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 16, 47
	add %r8, %r8, %r7
	lbz %r7, 3(%r3)
	rldicr %r7, %r7, 24, 39
	add %r8, %r8, %r7
	lbz %r7, 4(%r3)
	rldicr %r7, %r7, 32, 31
	add %r8, %r8, %r7
	rldicr %r7, %r8, 54, 9
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 44, 19
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 34, 29
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 24, 39
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 12(%r6)
	addi %r3, %r3, 5
	addi %r6, %r6, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
	li %r11, 128
25:
	lbz %r8, 0(%r3)
	rldicr %r7, %r8, 60, 3
	rldicl %r7, %r7, 4, 60
	mulld %r7, %r7, %r9
	addi %r7, %r7, 8
	rldicl %r7, %r7, 60, 4
	stw %r7, 0(%r6)
	rldicl %r7, %r8, 60, 4
	mulld %r7, %r7, %r9
	addi %r7, %r7, 8
	rldicl %r7, %r7, 60, 4
	stw %r7, 4(%r6)
	addi %r3, %r3, 1
	addi %r6, %r6, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
23:
	b 21f
20:
	li %r11, 32
26:
	lbz %r8, 0(%r3)
	rldicr %r7, %r8, 63, 0
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 62, 1
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 61, 2
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 60, 3
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 12(%r6)
	rldicr %r7, %r8, 59, 4
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 16(%r6)
	rldicr %r7, %r8, 58, 5
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 20(%r6)
	rldicr %r7, %r8, 57, 6
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 24(%r6)
	rldicr %r7, %r8, 56, 7
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 28(%r6)
	addi %r3, %r3, 1
	addi %r6, %r6, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
21:
	blr
