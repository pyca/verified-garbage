// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5:
	stdu %r1, -1056(%r1)
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
	addi %r3, %r21, 432
	addi %r4, %r21, 512
	bl {vg_hmac_md5_init_core}
	li %r12, 1
	li %r11, 704
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 432(%r21)
	stw %r8, 592(%r21)
	lwz %r8, 436(%r21)
	stw %r8, 596(%r21)
	lwz %r8, 440(%r21)
	stw %r8, 600(%r21)
	lwz %r8, 444(%r21)
	stw %r8, 604(%r21)
	lwz %r8, 448(%r21)
	stw %r8, 608(%r21)
	lwz %r8, 452(%r21)
	stw %r8, 612(%r21)
	lwz %r8, 456(%r21)
	stw %r8, 616(%r21)
	lwz %r8, 460(%r21)
	stw %r8, 620(%r21)
	lwz %r8, 464(%r21)
	stw %r8, 624(%r21)
	lwz %r8, 468(%r21)
	stw %r8, 628(%r21)
	lwz %r8, 472(%r21)
	stw %r8, 632(%r21)
	lwz %r8, 476(%r21)
	stw %r8, 636(%r21)
	lwz %r8, 480(%r21)
	stw %r8, 640(%r21)
	lwz %r8, 484(%r21)
	stw %r8, 644(%r21)
	lwz %r8, 488(%r21)
	stw %r8, 648(%r21)
	lwz %r8, 492(%r21)
	stw %r8, 652(%r21)
	lwz %r8, 496(%r21)
	stw %r8, 656(%r21)
	lwz %r8, 500(%r21)
	stw %r8, 660(%r21)
	lwz %r8, 504(%r21)
	stw %r8, 664(%r21)
	lwz %r8, 508(%r21)
	stw %r8, 668(%r21)
	addi %r3, %r21, 592
	li %r4, 64
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_md5_update_scratch}
	addi %r3, %r21, 592
	addi %r4, %r20, 64
	addi %r5, %r21, 704
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_md5_update_scratch}
	addi %r3, %r21, 592
	addi %r4, %r21, 512
	addi %r5, %r20, 68
	addi %r6, %r21, 672
	addi %r7, %r21, 48
	bl {vg_hmac_md5_finalize_scratch}
	lwz %r8, 672(%r21)
	stw %r8, 688(%r21)
	lwz %r8, 676(%r21)
	stw %r8, 692(%r21)
	lwz %r8, 680(%r21)
	stw %r8, 696(%r21)
	lwz %r8, 684(%r21)
	stw %r8, 700(%r21)
	addi %r3, %r21, 432
	addi %r4, %r21, 672
	addi %r5, %r22, -1
	addi %r6, %r21, 688
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_md5_iterate}
	addi %r12, %r24, -16
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 16
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 688(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 704
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
	addi %r1, %r1, 1056
	li %r0, 0
	stdu %r1, -1616(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	addi %r1, %r1, 1616
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr
