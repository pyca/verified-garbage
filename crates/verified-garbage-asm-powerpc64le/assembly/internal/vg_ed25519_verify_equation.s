// The functions of `src/internal/vg_ed25519_verify_equation.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_verify_equation:
	std %r14, 1024(%r6)
	std %r15, 1032(%r6)
	std %r16, 1040(%r6)
	std %r17, 1048(%r6)
	std %r18, 1056(%r6)
	std %r19, 1064(%r6)
	std %r26, 1072(%r6)
	std %r27, 1080(%r6)
	std %r28, 1088(%r6)
	std %r29, 1096(%r6)
	std %r30, 1104(%r6)
	std %r31, 1112(%r6)
	addi %r29, %r3, 0
	addi %r30, %r4, 0
	addi %r31, %r5, 0
	mflr %r7
	std %r7, 1120(%r6)
	addi %r14, %r30, 32
	lwz %r7, 0(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 188(%r6)
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
	li %r17, 0
	b 21f
20:
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
	addi %r27, %r29, 0
	li %r28, 7776
	li %r18, 1
22:
	addi %r14, %r27, 0
	lwz %r7, 0(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 124(%r6)
	rldicl %r8, %r7, 33, 31
	std %r8, 24(%r6)
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 124(%r6)
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
	li %r5, 0
	lwz %r7, 96(%r6)
	lwz %r8, 864(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 100(%r6)
	lwz %r8, 868(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 104(%r6)
	lwz %r8, 872(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 108(%r6)
	lwz %r8, 876(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 112(%r6)
	lwz %r8, 880(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 116(%r6)
	lwz %r8, 884(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 120(%r6)
	lwz %r8, 888(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 124(%r6)
	lwz %r8, 892(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 23f
	li %r17, 0
	b 24f
23:
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
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 192(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 196(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 200(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 204(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 208(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 212(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 216(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 220(%r6)
	addi %r3, %r6, 0
	li %r4, 224
	li %r5, 96
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	ld %r8, 224(%r6)
	ld %r4, 192(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 200(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 208(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 216(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	addi %r3, %r6, 0
	li %r4, 288
	li %r5, 576
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 288
	li %r5, 288
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	ld %r8, 288(%r6)
	ld %r4, 192(%r6)
	addc %r8, %r8, %r4
	ld %r9, 296(%r6)
	ld %r4, 200(%r6)
	adde %r9, %r9, %r4
	ld %r10, 304(%r6)
	ld %r4, 208(%r6)
	adde %r10, %r10, %r4
	ld %r11, 312(%r6)
	ld %r4, 216(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	addi %r3, %r6, 0
	li %r4, 320
	li %r5, 288
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 352
	li %r5, 320
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 352
	li %r6, 352
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 384
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 128
	li %r5, 256
	li %r6, 384
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	bl {vg_gf25519_r32_pow250}
	addi %r6, %r3, 0
	li %r12, 2
25:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	addi %r3, %r6, 0
	li %r4, 544
	li %r5, 544
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	ld %r8, 224(%r6)
	ld %r4, 256(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 264(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 272(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 280(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 448(%r6)
	std %r9, 456(%r6)
	std %r10, 464(%r6)
	std %r11, 472(%r6)
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 256
	li %r6, 352
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 288
	li %r6, 64
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 416
	li %r6, 64
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	ld %r8, 416(%r6)
	ld %r4, 256(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 424(%r6)
	ld %r4, 264(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 432(%r6)
	ld %r4, 272(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 440(%r6)
	ld %r4, 280(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 26f
	ld %r8, 416(%r6)
	ld %r4, 448(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 424(%r6)
	ld %r4, 456(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 432(%r6)
	ld %r4, 464(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 440(%r6)
	ld %r4, 472(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 28f
	li %r17, 0
	b 29f
28:
	lis %r7, 18958
	ori %r7, %r7, 41136
	stw %r7, 640(%r6)
	lis %r7, -15122
	ori %r7, %r7, 6951
	stw %r7, 644(%r6)
	lis %r7, -21201
	ori %r7, %r7, 58488
	stw %r7, 648(%r6)
	lis %r7, 12099
	ori %r7, %r7, 6150
	stw %r7, 652(%r6)
	lis %r7, 15867
	ori %r7, %r7, 55207
	stw %r7, 656(%r6)
	lis %r7, 11085
	ori %r7, %r7, 153
	stw %r7, 660(%r6)
	lis %r7, 20417
	ori %r7, %r7, 57099
	stw %r7, 664(%r6)
	lis %r7, 11139
	ori %r7, %r7, 9344
	stw %r7, 668(%r6)
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 640
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 210f
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
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 212f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	ld %r8, 224(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	b 213f
212:
213:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 211f
210:
	ld %r5, 24(%r6)
	cmpldi %cr0, %r5, 0
	bne %cr0, 214f
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
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 216f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	ld %r8, 224(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	b 217f
216:
217:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 215f
214:
	li %r17, 0
215:
211:
29:
	b 27f
26:
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 218f
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
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 220f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	ld %r8, 224(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	b 221f
220:
221:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 219f
218:
	ld %r5, 24(%r6)
	cmpldi %cr0, %r5, 0
	bne %cr0, 222f
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
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 224f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	ld %r8, 224(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 232(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 240(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 248(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	b 225f
224:
225:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 223f
222:
	li %r17, 0
223:
219:
27:
24:
	and %r18, %r18, %r17
	add %r14, %r6, %r28
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
	addi %r27, %r30, 0
	addi %r28, %r28, 128
	addi %r7, %r28, -8032
	cmpldi %cr0, %r7, 0
	bne %cr0, 22b
	cmpldi %cr0, %r18, 0
	bne %cr0, 226f
	li %r17, 0
	b 227f
226:
	addi %r14, %r6, 7776
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
	ld %r8, 640(%r6)
	ld %r4, 608(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 648(%r6)
	ld %r4, 616(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 656(%r6)
	ld %r4, 624(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 664(%r6)
	ld %r4, 632(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	ld %r8, 640(%r6)
	ld %r4, 608(%r6)
	addc %r8, %r8, %r4
	ld %r9, 648(%r6)
	ld %r4, 616(%r6)
	adde %r9, %r9, %r4
	ld %r10, 656(%r6)
	ld %r4, 624(%r6)
	adde %r10, %r10, %r4
	ld %r11, 664(%r6)
	ld %r4, 632(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	ld %r8, 704(%r6)
	ld %r4, 704(%r6)
	addc %r8, %r8, %r4
	ld %r9, 712(%r6)
	ld %r4, 712(%r6)
	adde %r9, %r9, %r4
	ld %r10, 720(%r6)
	ld %r4, 720(%r6)
	adde %r10, %r10, %r4
	ld %r11, 728(%r6)
	ld %r4, 728(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	ld %r8, 672(%r6)
	ld %r4, 672(%r6)
	addc %r8, %r8, %r4
	ld %r9, 680(%r6)
	ld %r4, 680(%r6)
	adde %r9, %r9, %r4
	ld %r10, 688(%r6)
	ld %r4, 688(%r6)
	adde %r10, %r10, %r4
	ld %r11, 696(%r6)
	ld %r4, 696(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
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
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 192(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 196(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 200(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 204(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 208(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 212(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 216(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 220(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 224(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 228(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 232(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 236(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 240(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 244(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 248(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 252(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 256(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 260(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 264(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 268(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 272(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 276(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 280(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 284(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 288(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 292(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 296(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 300(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 304(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 308(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 312(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 316(%r6)
	li %r16, 1
228:
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 320(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 328(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 320(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 336(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 328(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 320(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 336(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 328(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 320(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 344(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 336(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 328(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 344(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 336(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	addc %r8, %r8, %r4
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	adde %r9, %r9, %r4
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	adde %r10, %r10, %r4
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 352(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 360(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 352(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 368(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 360(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 352(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 368(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 360(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 352(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 376(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 368(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 360(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 376(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 368(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 448(%r6)
	std %r9, 456(%r6)
	std %r10, 464(%r6)
	std %r11, 472(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 480(%r6)
	std %r9, 488(%r6)
	std %r10, 496(%r6)
	std %r11, 504(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	addc %r8, %r8, %r4
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	adde %r9, %r9, %r4
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	adde %r10, %r10, %r4
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	addc %r8, %r8, %r4
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	adde %r9, %r9, %r4
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	adde %r10, %r10, %r4
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 480(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 488(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 480(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 496(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 488(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 480(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 496(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 488(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 480(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 504(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 496(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 488(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 504(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 496(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
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
	ld %r8, 640(%r6)
	ld %r4, 608(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 648(%r6)
	ld %r4, 616(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 656(%r6)
	ld %r4, 624(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 664(%r6)
	ld %r4, 632(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	ld %r8, 640(%r6)
	ld %r4, 608(%r6)
	addc %r8, %r8, %r4
	ld %r9, 648(%r6)
	ld %r4, 616(%r6)
	adde %r9, %r9, %r4
	ld %r10, 656(%r6)
	ld %r4, 624(%r6)
	adde %r10, %r10, %r4
	ld %r11, 664(%r6)
	ld %r4, 632(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	ld %r8, 704(%r6)
	ld %r4, 704(%r6)
	addc %r8, %r8, %r4
	ld %r9, 712(%r6)
	ld %r4, 712(%r6)
	adde %r9, %r9, %r4
	ld %r10, 720(%r6)
	ld %r4, 720(%r6)
	adde %r10, %r10, %r4
	ld %r11, 728(%r6)
	ld %r4, 728(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	ld %r8, 672(%r6)
	ld %r4, 672(%r6)
	addc %r8, %r8, %r4
	ld %r9, 680(%r6)
	ld %r4, 680(%r6)
	adde %r9, %r9, %r4
	ld %r10, 688(%r6)
	ld %r4, 688(%r6)
	adde %r10, %r10, %r4
	ld %r11, 696(%r6)
	ld %r4, 696(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
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
	addi %r16, %r16, 1
	addi %r7, %r16, -15
	cmpldi %cr0, %r7, 0
	bne %cr0, 228b
	bcl 20, 31, 2f
2:
	mflr %r19
	addis %r19, %r19, ({VG_ED25519_VERIFY_NEG_BASE}
	addi %r19, %r19, ({VG_ED25519_VERIFY_NEG_BASE}
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
	li %r8, 0
	lbz %r9, 32(%r31)
	or %r8, %r8, %r9
	lbz %r9, 33(%r31)
	or %r8, %r8, %r9
	lbz %r9, 34(%r31)
	or %r8, %r8, %r9
	lbz %r9, 35(%r31)
	or %r8, %r8, %r9
	lbz %r9, 36(%r31)
	or %r8, %r8, %r9
	lbz %r9, 37(%r31)
	or %r8, %r8, %r9
	lbz %r9, 38(%r31)
	or %r8, %r8, %r9
	lbz %r9, 39(%r31)
	or %r8, %r8, %r9
	lbz %r9, 40(%r31)
	or %r8, %r8, %r9
	lbz %r9, 41(%r31)
	or %r8, %r8, %r9
	lbz %r9, 42(%r31)
	or %r8, %r8, %r9
	lbz %r9, 43(%r31)
	or %r8, %r8, %r9
	lbz %r9, 44(%r31)
	or %r8, %r8, %r9
	lbz %r9, 45(%r31)
	or %r8, %r8, %r9
	lbz %r9, 46(%r31)
	or %r8, %r8, %r9
	lbz %r9, 47(%r31)
	or %r8, %r8, %r9
	lbz %r9, 48(%r31)
	or %r8, %r8, %r9
	lbz %r9, 49(%r31)
	or %r8, %r8, %r9
	lbz %r9, 50(%r31)
	or %r8, %r8, %r9
	lbz %r9, 51(%r31)
	or %r8, %r8, %r9
	lbz %r9, 52(%r31)
	or %r8, %r8, %r9
	lbz %r9, 53(%r31)
	or %r8, %r8, %r9
	lbz %r9, 54(%r31)
	or %r8, %r8, %r9
	lbz %r9, 55(%r31)
	or %r8, %r8, %r9
	lbz %r9, 56(%r31)
	or %r8, %r8, %r9
	lbz %r9, 57(%r31)
	or %r8, %r8, %r9
	lbz %r9, 58(%r31)
	or %r8, %r8, %r9
	lbz %r9, 59(%r31)
	or %r8, %r8, %r9
	lbz %r9, 60(%r31)
	or %r8, %r8, %r9
	lbz %r9, 61(%r31)
	or %r8, %r8, %r9
	lbz %r9, 62(%r31)
	or %r8, %r8, %r9
	lbz %r9, 63(%r31)
	or %r8, %r8, %r9
	cmpldi %cr0, %r8, 0
	beq %cr0, 229f
	li %r15, 128
	b 230f
229:
	li %r15, 64
230:
231:
	addi %r15, %r15, -1
	li %r26, 4
232:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 64(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 72(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 64(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 80(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 72(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 64(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 80(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 72(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 64(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 88(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 80(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 72(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 88(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 80(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 96(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 104(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 96(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 112(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 104(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 96(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 120(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 112(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 104(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 96(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 120(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 112(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 104(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 120(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 112(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 120(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	ld %r8, 384(%r6)
	ld %r4, 384(%r6)
	addc %r8, %r8, %r4
	ld %r9, 392(%r6)
	ld %r4, 392(%r6)
	adde %r9, %r9, %r4
	ld %r10, 400(%r6)
	ld %r4, 400(%r6)
	adde %r10, %r10, %r4
	ld %r11, 408(%r6)
	ld %r4, 408(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 64(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 72(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 64(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 80(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 72(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 64(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 80(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 72(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 64(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 88(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 80(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 72(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 88(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 80(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 416(%r6)
	ld %r4, 416(%r6)
	addc %r8, %r8, %r4
	ld %r9, 424(%r6)
	ld %r4, 424(%r6)
	adde %r9, %r9, %r4
	ld %r10, 432(%r6)
	ld %r4, 432(%r6)
	adde %r10, %r10, %r4
	ld %r11, 440(%r6)
	ld %r4, 440(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 448(%r6)
	std %r9, 456(%r6)
	std %r10, 464(%r6)
	std %r11, 472(%r6)
	ld %r8, 384(%r6)
	ld %r4, 448(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 392(%r6)
	ld %r4, 456(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 400(%r6)
	ld %r4, 464(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 408(%r6)
	ld %r4, 472(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 480(%r6)
	std %r9, 488(%r6)
	std %r10, 496(%r6)
	std %r11, 504(%r6)
	ld %r8, 320(%r6)
	ld %r4, 352(%r6)
	addc %r8, %r8, %r4
	ld %r9, 328(%r6)
	ld %r4, 360(%r6)
	adde %r9, %r9, %r4
	ld %r10, 336(%r6)
	ld %r4, 368(%r6)
	adde %r10, %r10, %r4
	ld %r11, 344(%r6)
	ld %r4, 376(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 416(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 424(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 416(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 432(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 424(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 416(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 432(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 424(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 416(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 440(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 432(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 424(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 440(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 432(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 480(%r6)
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 488(%r6)
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 480(%r6)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 496(%r6)
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 488(%r6)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 480(%r6)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 496(%r6)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 488(%r6)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 480(%r6)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 504(%r6)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 496(%r6)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 488(%r6)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 504(%r6)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 496(%r6)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 232b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 416(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 424(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 416(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 432(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 424(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 416(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 432(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 424(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 416(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 440(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 432(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 424(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 440(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 432(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	rldicl %r8, %r15, 63, 1
	add %r8, %r31, %r8
	lbz %r9, 0(%r8)
	rldicl %r10, %r9, 60, 4
	rldicr %r9, %r9, 60, 3
	rldicl %r9, %r9, 4, 60
	subf %r10, %r9, %r10
	rldicr %r8, %r15, 63, 0
	rldicl %r8, %r8, 1, 63
	mulld %r10, %r10, %r8
	add %r9, %r9, %r10
	cmpldi %cr0, %r9, 0
	bne %cr0, 233f
	b 234f
233:
	addi %r16, %r9, -1
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 192(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 196(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 200(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 204(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 208(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 212(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 216(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 220(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 224(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 228(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 232(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 236(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 240(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 244(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 248(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 252(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 256(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 260(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 264(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 268(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 272(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 276(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 280(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 284(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 288(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 292(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 296(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 300(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 304(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 308(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 312(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 316(%r6)
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 320(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 328(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 320(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 336(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 328(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 320(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 336(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 328(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 320(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 344(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 336(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 328(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 344(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 336(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	addc %r8, %r8, %r4
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	adde %r9, %r9, %r4
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	adde %r10, %r10, %r4
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 352(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 360(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 352(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 368(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 360(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 352(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 368(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 360(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 352(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 376(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 368(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 360(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 376(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 368(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 448(%r6)
	std %r9, 456(%r6)
	std %r10, 464(%r6)
	std %r11, 472(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 480(%r6)
	std %r9, 488(%r6)
	std %r10, 496(%r6)
	std %r11, 504(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	addc %r8, %r8, %r4
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	adde %r9, %r9, %r4
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	adde %r10, %r10, %r4
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	addc %r8, %r8, %r4
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	adde %r9, %r9, %r4
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	adde %r10, %r10, %r4
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 480(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 488(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 480(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 496(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 488(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 480(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 496(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 488(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 480(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 504(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 496(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 488(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 504(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 496(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
234:
	rldicl %r7, %r15, 58, 6
	cmpldi %cr0, %r7, 0
	beq %cr0, 235f
	b 236f
235:
	rldicl %r8, %r15, 63, 1
	add %r8, %r30, %r8
	lbz %r9, 32(%r8)
	rldicl %r10, %r9, 60, 4
	rldicr %r9, %r9, 60, 3
	rldicl %r9, %r9, 4, 60
	subf %r10, %r9, %r10
	rldicr %r8, %r15, 63, 0
	rldicl %r8, %r8, 1, 63
	mulld %r10, %r10, %r8
	add %r9, %r9, %r10
	cmpldi %cr0, %r9, 0
	bne %cr0, 237f
	b 238f
237:
	addi %r7, %r9, -1
	rldicr %r7, %r7, 7, 56
	add %r14, %r19, %r7
	lwz %r7, 0(%r14)
	stw %r7, 192(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 196(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 200(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 204(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 208(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 212(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 216(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 220(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 224(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 228(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 232(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 236(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 240(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 244(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 248(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 252(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 256(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 260(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 264(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 268(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 272(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 276(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 280(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 284(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 288(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 292(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 296(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 300(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 304(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 308(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 312(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 316(%r6)
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 320(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 328(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 320(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 336(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 328(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 320(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 336(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 328(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 320(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 344(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 336(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 328(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 344(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 336(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	ld %r8, 96(%r6)
	ld %r4, 64(%r6)
	addc %r8, %r8, %r4
	ld %r9, 104(%r6)
	ld %r4, 72(%r6)
	adde %r9, %r9, %r4
	ld %r10, 112(%r6)
	ld %r4, 80(%r6)
	adde %r10, %r10, %r4
	ld %r11, 120(%r6)
	ld %r4, 88(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 352(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 360(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 352(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 368(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 360(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 352(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 368(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 360(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 352(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 376(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 368(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 360(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 376(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 368(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 448(%r6)
	std %r9, 456(%r6)
	std %r10, 464(%r6)
	std %r11, 472(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 480(%r6)
	std %r9, 488(%r6)
	std %r10, 496(%r6)
	std %r11, 504(%r6)
	ld %r8, 416(%r6)
	ld %r4, 384(%r6)
	addc %r8, %r8, %r4
	ld %r9, 424(%r6)
	ld %r4, 392(%r6)
	adde %r9, %r9, %r4
	ld %r10, 432(%r6)
	ld %r4, 400(%r6)
	adde %r10, %r10, %r4
	ld %r11, 440(%r6)
	ld %r4, 408(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	ld %r8, 352(%r6)
	ld %r4, 320(%r6)
	addc %r8, %r8, %r4
	ld %r9, 360(%r6)
	ld %r4, 328(%r6)
	adde %r9, %r9, %r4
	ld %r10, 368(%r6)
	ld %r4, 336(%r6)
	adde %r10, %r10, %r4
	ld %r11, 376(%r6)
	ld %r4, 344(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 480(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 488(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 480(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 496(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 488(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 480(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 496(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 488(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 480(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 504(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 496(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 488(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 504(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 496(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
238:
236:
	cmpldi %cr0, %r15, 0
	bne %cr0, 231b
	addi %r14, %r6, 7904
	lwz %r7, 0(%r14)
	stw %r7, 192(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 196(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 200(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 204(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 208(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 212(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 216(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 220(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 224(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 228(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 232(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 236(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 240(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 244(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 248(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 252(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 256(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 260(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 264(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 268(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 272(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 276(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 280(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 284(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 288(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 292(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 296(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 300(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 304(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 308(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 312(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 316(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 320(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 324(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 328(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 332(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 336(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 340(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 344(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 348(%r6)
	ld %r8, 320(%r6)
	ld %r4, 192(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 328(%r6)
	ld %r4, 200(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 336(%r6)
	ld %r4, 208(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 344(%r6)
	ld %r4, 216(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	ld %r8, 320(%r6)
	ld %r4, 288(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 328(%r6)
	ld %r4, 296(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 336(%r6)
	ld %r4, 304(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 344(%r6)
	ld %r4, 312(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	addi %r3, %r6, 0
	li %r4, 320
	li %r5, 64
	li %r6, 256
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 352
	li %r5, 192
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 96
	li %r6, 256
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 224
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	ld %r8, 320(%r6)
	ld %r4, 352(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 328(%r6)
	ld %r4, 360(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 336(%r6)
	ld %r4, 368(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 344(%r6)
	ld %r4, 376(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 239f
	li %r17, 0
	b 240f
239:
	ld %r8, 384(%r6)
	ld %r4, 416(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 392(%r6)
	ld %r4, 424(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 400(%r6)
	ld %r4, 432(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 408(%r6)
	ld %r4, 440(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 241f
	li %r17, 0
	b 242f
241:
	li %r17, 1
242:
240:
227:
21:
	ld %r7, 1120(%r6)
	mtlr %r7
	addi %r3, %r17, 0
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
