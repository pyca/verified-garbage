// The functions of `src/internal/vg_ed25519_scalar_base.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_base:
	std %r14, 1024(%r5)
	std %r15, 1032(%r5)
	std %r16, 1040(%r5)
	std %r17, 1048(%r5)
	std %r18, 1056(%r5)
	std %r19, 1064(%r5)
	std %r26, 1072(%r5)
	std %r27, 1080(%r5)
	std %r28, 1088(%r5)
	std %r29, 1096(%r5)
	std %r30, 1104(%r5)
	std %r31, 1112(%r5)
	addi %r6, %r5, 0
	addi %r27, %r3, 0
	mflr %r7
	std %r7, 1120(%r6)
	addi %r14, %r4, 0
	li %r7, 0
	stw %r7, 64(%r6)
	stw %r7, 68(%r6)
	stw %r7, 72(%r6)
	stw %r7, 76(%r6)
	stw %r7, 80(%r6)
	stw %r7, 84(%r6)
	stw %r7, 88(%r6)
	stw %r7, 92(%r6)
	stw %r7, 96(%r6)
	stw %r7, 100(%r6)
	stw %r7, 104(%r6)
	stw %r7, 108(%r6)
	stw %r7, 112(%r6)
	stw %r7, 116(%r6)
	stw %r7, 120(%r6)
	stw %r7, 124(%r6)
	stw %r7, 128(%r6)
	stw %r7, 132(%r6)
	stw %r7, 136(%r6)
	stw %r7, 140(%r6)
	stw %r7, 144(%r6)
	stw %r7, 148(%r6)
	stw %r7, 152(%r6)
	stw %r7, 156(%r6)
	stw %r7, 160(%r6)
	stw %r7, 164(%r6)
	stw %r7, 168(%r6)
	stw %r7, 172(%r6)
	stw %r7, 176(%r6)
	stw %r7, 180(%r6)
	stw %r7, 184(%r6)
	stw %r7, 188(%r6)
	stw %r7, 192(%r6)
	stw %r7, 196(%r6)
	stw %r7, 200(%r6)
	stw %r7, 204(%r6)
	stw %r7, 208(%r6)
	stw %r7, 212(%r6)
	stw %r7, 216(%r6)
	stw %r7, 220(%r6)
	stw %r7, 224(%r6)
	stw %r7, 228(%r6)
	stw %r7, 232(%r6)
	stw %r7, 236(%r6)
	stw %r7, 240(%r6)
	stw %r7, 244(%r6)
	stw %r7, 248(%r6)
	stw %r7, 252(%r6)
	stw %r7, 256(%r6)
	stw %r7, 260(%r6)
	stw %r7, 264(%r6)
	stw %r7, 268(%r6)
	stw %r7, 272(%r6)
	stw %r7, 276(%r6)
	stw %r7, 280(%r6)
	stw %r7, 284(%r6)
	stw %r7, 288(%r6)
	stw %r7, 292(%r6)
	stw %r7, 296(%r6)
	stw %r7, 300(%r6)
	stw %r7, 304(%r6)
	stw %r7, 308(%r6)
	stw %r7, 312(%r6)
	stw %r7, 316(%r6)
	stw %r7, 320(%r6)
	stw %r7, 324(%r6)
	stw %r7, 328(%r6)
	stw %r7, 332(%r6)
	stw %r7, 336(%r6)
	stw %r7, 340(%r6)
	stw %r7, 344(%r6)
	stw %r7, 348(%r6)
	stw %r7, 352(%r6)
	stw %r7, 356(%r6)
	stw %r7, 360(%r6)
	stw %r7, 364(%r6)
	stw %r7, 368(%r6)
	stw %r7, 372(%r6)
	stw %r7, 376(%r6)
	stw %r7, 380(%r6)
	stw %r7, 384(%r6)
	stw %r7, 388(%r6)
	stw %r7, 392(%r6)
	stw %r7, 396(%r6)
	stw %r7, 400(%r6)
	stw %r7, 404(%r6)
	stw %r7, 408(%r6)
	stw %r7, 412(%r6)
	stw %r7, 416(%r6)
	stw %r7, 420(%r6)
	stw %r7, 424(%r6)
	stw %r7, 428(%r6)
	stw %r7, 432(%r6)
	stw %r7, 436(%r6)
	stw %r7, 440(%r6)
	stw %r7, 444(%r6)
	stw %r7, 448(%r6)
	stw %r7, 452(%r6)
	stw %r7, 456(%r6)
	stw %r7, 460(%r6)
	stw %r7, 464(%r6)
	stw %r7, 468(%r6)
	stw %r7, 472(%r6)
	stw %r7, 476(%r6)
	stw %r7, 480(%r6)
	stw %r7, 484(%r6)
	stw %r7, 488(%r6)
	stw %r7, 492(%r6)
	stw %r7, 496(%r6)
	stw %r7, 500(%r6)
	stw %r7, 504(%r6)
	stw %r7, 508(%r6)
	stw %r7, 512(%r6)
	stw %r7, 516(%r6)
	stw %r7, 520(%r6)
	stw %r7, 524(%r6)
	stw %r7, 528(%r6)
	stw %r7, 532(%r6)
	stw %r7, 536(%r6)
	stw %r7, 540(%r6)
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	stw %r7, 576(%r6)
	stw %r7, 580(%r6)
	stw %r7, 584(%r6)
	stw %r7, 588(%r6)
	stw %r7, 592(%r6)
	stw %r7, 596(%r6)
	stw %r7, 600(%r6)
	stw %r7, 604(%r6)
	stw %r7, 608(%r6)
	stw %r7, 612(%r6)
	stw %r7, 616(%r6)
	stw %r7, 620(%r6)
	stw %r7, 624(%r6)
	stw %r7, 628(%r6)
	stw %r7, 632(%r6)
	stw %r7, 636(%r6)
	stw %r7, 640(%r6)
	stw %r7, 644(%r6)
	stw %r7, 648(%r6)
	stw %r7, 652(%r6)
	stw %r7, 656(%r6)
	stw %r7, 660(%r6)
	stw %r7, 664(%r6)
	stw %r7, 668(%r6)
	stw %r7, 672(%r6)
	stw %r7, 676(%r6)
	stw %r7, 680(%r6)
	stw %r7, 684(%r6)
	stw %r7, 688(%r6)
	stw %r7, 692(%r6)
	stw %r7, 696(%r6)
	stw %r7, 700(%r6)
	stw %r7, 704(%r6)
	stw %r7, 708(%r6)
	stw %r7, 712(%r6)
	stw %r7, 716(%r6)
	stw %r7, 720(%r6)
	stw %r7, 724(%r6)
	stw %r7, 728(%r6)
	stw %r7, 732(%r6)
	stw %r7, 736(%r6)
	stw %r7, 740(%r6)
	stw %r7, 744(%r6)
	stw %r7, 748(%r6)
	stw %r7, 752(%r6)
	stw %r7, 756(%r6)
	stw %r7, 760(%r6)
	stw %r7, 764(%r6)
	lis %r7, -28891
	ori %r7, %r7, 54554
	stw %r7, 64(%r6)
	lis %r7, -13994
	ori %r7, %r7, 11616
	stw %r7, 68(%r6)
	lis %r7, -27355
	ori %r7, %r7, 42930
	stw %r7, 72(%r6)
	lis %r7, 26924
	ori %r7, %r7, 51040
	stw %r7, 76(%r6)
	lis %r7, -554
	ori %r7, %r7, 56412
	stw %r7, 80(%r6)
	lis %r7, -16220
	ori %r7, %r7, 57905
	stw %r7, 84(%r6)
	lis %r7, -12946
	ori %r7, %r7, 21502
	stw %r7, 88(%r6)
	lis %r7, 8553
	ori %r7, %r7, 14035
	stw %r7, 92(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26200
	stw %r7, 96(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 100(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 104(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 108(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 112(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 116(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 120(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, -23113
	ori %r7, %r7, 56739
	stw %r7, 160(%r6)
	lis %r7, 28126
	ori %r7, %r7, 35507
	stw %r7, 164(%r6)
	lis %r7, 30545
	ori %r7, %r7, 21237
	stw %r7, 168(%r6)
	lis %r7, 8432
	ori %r7, %r7, 40832
	stw %r7, 172(%r6)
	lis %r7, 25771
	ori %r7, %r7, 58237
	stw %r7, 176(%r6)
	lis %r7, 26346
	ori %r7, %r7, 20110
	stw %r7, 180(%r6)
	lis %r7, -10357
	ori %r7, %r7, 30309
	stw %r7, 184(%r6)
	lis %r7, 26503
	ori %r7, %r7, 24335
	stw %r7, 188(%r6)
	addi %r19, %r14, 0
	lis %r7, 4953
	ori %r7, %r7, 30883
	stw %r7, 576(%r6)
	lis %r7, 30187
	ori %r7, %r7, 19914
	stw %r7, 580(%r6)
	lis %r7, 16705
	ori %r7, %r7, 55467
	stw %r7, 584(%r6)
	lis %r7, 112
	ori %r7, %r7, 2637
	stw %r7, 588(%r6)
	lis %r7, 30585
	ori %r7, %r7, 59544
	stw %r7, 592(%r6)
	lis %r7, -29497
	ori %r7, %r7, 16505
	stw %r7, 596(%r6)
	lis %r7, 11119
	ori %r7, %r7, 65139
	stw %r7, 600(%r6)
	lis %r7, 20995
	ori %r7, %r7, 27886
	stw %r7, 604(%r6)
	li %r16, 0
20:
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	li %r15, 16
21:
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r15, %r15, -1
	cmpldi %cr0, %r15, 0
	bne %cr0, 21b
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 20b
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 168(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 172(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 176(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 180(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 184(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 188(%r6)
	li %r26, 16
22:
	addi %r26, %r26, -1
	addi %r16, %r26, 0
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	li %r16, 0
23:
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 23b
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	rldicr %r7, %r26, 1, 62
	add %r14, %r19, %r7
	lbz %r7, 0(%r14)
	lbz %r8, 1(%r14)
	rldicr %r8, %r8, 8, 55
	add %r7, %r7, %r8
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 32(%r6)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 33(%r6)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 34(%r6)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 35(%r6)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 36(%r6)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 37(%r6)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 38(%r6)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 39(%r6)
	rldicr %r8, %r7, 55, 8
	rldicl %r8, %r8, 1, 63
	stb %r8, 40(%r6)
	rldicr %r8, %r7, 54, 9
	rldicl %r8, %r8, 1, 63
	stb %r8, 41(%r6)
	rldicr %r8, %r7, 53, 10
	rldicl %r8, %r8, 1, 63
	stb %r8, 42(%r6)
	rldicr %r8, %r7, 52, 11
	rldicl %r8, %r8, 1, 63
	stb %r8, 43(%r6)
	rldicr %r8, %r7, 51, 12
	rldicl %r8, %r8, 1, 63
	stb %r8, 44(%r6)
	rldicr %r8, %r7, 50, 13
	rldicl %r8, %r8, 1, 63
	stb %r8, 45(%r6)
	rldicr %r8, %r7, 49, 14
	rldicl %r8, %r8, 1, 63
	stb %r8, 46(%r6)
	rldicr %r8, %r7, 48, 15
	rldicl %r8, %r8, 1, 63
	stb %r8, 47(%r6)
	li %r16, 16
24:
	addi %r16, %r16, -1
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	add %r7, %r6, %r16
	lbz %r7, 32(%r7)
	addi %r11, %r7, -1
	lwz %r5, 64(%r6)
	lwz %r7, 608(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 612(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 616(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 620(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 624(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 628(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 632(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 636(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 640(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 644(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 648(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 652(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 656(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 660(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 664(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 668(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 672(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 676(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 680(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 684(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 688(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 692(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 696(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 700(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 704(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 708(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 712(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 716(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 720(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 724(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 728(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 732(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 732(%r6)
	cmpldi %cr0, %r16, 0
	bne %cr0, 24b
	cmpldi %cr0, %r26, 0
	bne %cr0, 22b
	addi %r3, %r6, 0
	bl {vg_gf25519_r32_pow250}
	addi %r6, %r3, 0
	li %r12, 5
25:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
26:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	addi %r3, %r6, 0
	li %r4, 544
	li %r5, 544
	li %r6, 512
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 96
	li %r5, 96
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	lwz %r7, 64(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 892(%r6)
	lwz %r7, 892(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 892(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 924(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 924(%r6)
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 864(%r6)
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 868(%r6)
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 872(%r6)
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 876(%r6)
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 880(%r6)
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 884(%r6)
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 888(%r6)
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 892(%r6)
	lwz %r7, 864(%r6)
	rldicr %r17, %r7, 63, 0
	rldicl %r17, %r17, 32, 32
	lwz %r7, 96(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 892(%r6)
	lwz %r7, 892(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 892(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 924(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 924(%r6)
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 864(%r6)
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 868(%r6)
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 872(%r6)
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 876(%r6)
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 880(%r6)
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 884(%r6)
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 888(%r6)
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 892(%r6)
	lwz %r7, 892(%r6)
	add %r7, %r7, %r17
	stw %r7, 892(%r6)
	ld %r7, 1120(%r6)
	mtlr %r7
	addi %r14, %r27, 0
	lwz %r7, 864(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 868(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 872(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 876(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 880(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 884(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 888(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 892(%r6)
	stw %r7, 28(%r14)
	ld %r14, 1024(%r6)
	ld %r15, 1032(%r6)
	ld %r16, 1040(%r6)
	ld %r17, 1048(%r6)
	ld %r18, 1056(%r6)
	ld %r19, 1064(%r6)
	ld %r26, 1072(%r6)
	ld %r27, 1080(%r6)
	ld %r28, 1088(%r6)
	ld %r29, 1096(%r6)
	ld %r30, 1104(%r6)
	ld %r31, 1112(%r6)
	blr
