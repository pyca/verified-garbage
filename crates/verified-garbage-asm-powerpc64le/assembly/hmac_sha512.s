// The functions of `src/hmac_sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_init:
	rldicl %r12, %r6, 56, 8
	li %r11, 255
	and %r11, %r6, %r11
	addi %r11, %r11, 127
	rldicl %r11, %r11, 56, 8
	add %r12, %r12, %r11
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	stdu %r1, -1904(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 224(%r7)
	std %r21, 232(%r7)
	std %r22, 240(%r7)
	std %r23, 248(%r7)
	std %r24, 256(%r7)
	std %r25, 264(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r5, 0
	addi %r24, %r6, 0
	bl {vg_sha512_init}
	addi %r3, %r22, 0
	bl {vg_sha512_init}
	li %r12, 54
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
24:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r22, %r25
	stb %r8, 64(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	b 23f
22:
23:
	li %r10, 128
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
27:
	add %r11, %r22, %r25
	stb %r12, 64(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 27b
	b 26f
25:
26:
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r22, 64
	li %r6, 128
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	li %r12, 92
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
210:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r20, %r25
	stb %r8, 64(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 210b
	b 29f
28:
29:
	li %r10, 128
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 211f
213:
	add %r11, %r20, %r25
	stb %r12, 64(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 213b
	b 212f
211:
212:
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r20, 64
	li %r6, 128
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	ld %r20, 224(%r21)
	ld %r22, 240(%r21)
	ld %r23, 248(%r21)
	ld %r24, 256(%r21)
	ld %r25, 264(%r21)
	ld %r21, 232(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 1904
21:
	li %r0, 0
	stdu %r1, -1952(%r1)
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
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	addi %r1, %r1, 1952
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
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
20:
	stdu %r1, -1856(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 528(%r7)
	std %r21, 536(%r7)
	std %r22, 544(%r7)
	std %r23, 552(%r7)
	std %r24, 560(%r7)
	std %r25, 568(%r7)
	addi %r21, %r7, 0
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r6, 0
	addi %r25, %r5, 0
	addi %r20, %r7, 272
	addi %r3, %r20, 0
	bl {vg_sha512_init}
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r25, 0
	addi %r6, %r24, 0
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	addi %r3, %r20, 0
	addi %r4, %r24, 0
	addi %r5, %r21, 464
	addi %r6, %r21, 0
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r22, 0
	addi %r4, %r23, 0
	addi %r5, %r21, 464
	li %r6, 64
	addi %r7, %r21, 0
	ld %r20, 528(%r21)
	ld %r22, 544(%r21)
	ld %r23, 552(%r21)
	ld %r24, 560(%r21)
	ld %r25, 568(%r21)
	ld %r21, 536(%r21)
	bl {vg_hmac_sha512_init_scratch}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	std %r11, 224(%r12)
	std %r11, 232(%r12)
	std %r11, 240(%r12)
	std %r11, 248(%r12)
	std %r11, 256(%r12)
	std %r11, 264(%r12)
	std %r11, 272(%r12)
	std %r11, 280(%r12)
	std %r11, 288(%r12)
	std %r11, 296(%r12)
	std %r11, 304(%r12)
	std %r11, 312(%r12)
	std %r11, 320(%r12)
	std %r11, 328(%r12)
	std %r11, 336(%r12)
	std %r11, 344(%r12)
	std %r11, 352(%r12)
	std %r11, 360(%r12)
	std %r11, 368(%r12)
	std %r11, 376(%r12)
	std %r11, 384(%r12)
	std %r11, 392(%r12)
	std %r11, 400(%r12)
	std %r11, 408(%r12)
	std %r11, 416(%r12)
	std %r11, 424(%r12)
	std %r11, 432(%r12)
	std %r11, 440(%r12)
	std %r11, 448(%r12)
	std %r11, 456(%r12)
	std %r11, 464(%r12)
	std %r11, 472(%r12)
	std %r11, 480(%r12)
	std %r11, 488(%r12)
	std %r11, 496(%r12)
	std %r11, 504(%r12)
	std %r11, 512(%r12)
	std %r11, 520(%r12)
	std %r11, 528(%r12)
	std %r11, 536(%r12)
	std %r11, 544(%r12)
	std %r11, 552(%r12)
	std %r11, 560(%r12)
	std %r11, 568(%r12)
	addi %r1, %r1, 1856
	b 21b

vg_hmac_sha512_finalize:
	stdu %r1, -1904(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 224(%r7)
	std %r21, 232(%r7)
	std %r22, 240(%r7)
	std %r23, 248(%r7)
	std %r24, 256(%r7)
	std %r25, 264(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r6, 0
	addi %r4, %r5, 0
	addi %r5, %r7, 272
	addi %r6, %r7, 0
	bl {vg_sha512_finalize_scratch}
	lwz %r8, 0(%r22)
	stw %r8, 0(%r20)
	lwz %r8, 4(%r22)
	stw %r8, 4(%r20)
	lwz %r8, 8(%r22)
	stw %r8, 8(%r20)
	lwz %r8, 12(%r22)
	stw %r8, 12(%r20)
	lwz %r8, 16(%r22)
	stw %r8, 16(%r20)
	lwz %r8, 20(%r22)
	stw %r8, 20(%r20)
	lwz %r8, 24(%r22)
	stw %r8, 24(%r20)
	lwz %r8, 28(%r22)
	stw %r8, 28(%r20)
	lwz %r8, 32(%r22)
	stw %r8, 32(%r20)
	lwz %r8, 36(%r22)
	stw %r8, 36(%r20)
	lwz %r8, 40(%r22)
	stw %r8, 40(%r20)
	lwz %r8, 44(%r22)
	stw %r8, 44(%r20)
	lwz %r8, 48(%r22)
	stw %r8, 48(%r20)
	lwz %r8, 52(%r22)
	stw %r8, 52(%r20)
	lwz %r8, 56(%r22)
	stw %r8, 56(%r20)
	lwz %r8, 60(%r22)
	stw %r8, 60(%r20)
	addi %r3, %r20, 0
	li %r4, 128
	addi %r5, %r21, 272
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	addi %r3, %r20, 0
	li %r4, 192
	addi %r5, %r21, 272
	addi %r6, %r21, 0
	bl {vg_sha512_finalize_scratch}
	lwz %r8, 272(%r21)
	stw %r8, 0(%r23)
	lwz %r8, 276(%r21)
	stw %r8, 4(%r23)
	lwz %r8, 280(%r21)
	stw %r8, 8(%r23)
	lwz %r8, 284(%r21)
	stw %r8, 12(%r23)
	lwz %r8, 288(%r21)
	stw %r8, 16(%r23)
	lwz %r8, 292(%r21)
	stw %r8, 20(%r23)
	lwz %r8, 296(%r21)
	stw %r8, 24(%r23)
	lwz %r8, 300(%r21)
	stw %r8, 28(%r23)
	lwz %r8, 304(%r21)
	stw %r8, 32(%r23)
	lwz %r8, 308(%r21)
	stw %r8, 36(%r23)
	lwz %r8, 312(%r21)
	stw %r8, 40(%r23)
	lwz %r8, 316(%r21)
	stw %r8, 44(%r23)
	lwz %r8, 320(%r21)
	stw %r8, 48(%r23)
	lwz %r8, 324(%r21)
	stw %r8, 52(%r23)
	lwz %r8, 328(%r21)
	stw %r8, 56(%r23)
	lwz %r8, 332(%r21)
	stw %r8, 60(%r23)
	ld %r20, 224(%r21)
	ld %r22, 240(%r21)
	ld %r23, 248(%r21)
	ld %r24, 256(%r21)
	ld %r25, 264(%r21)
	ld %r21, 232(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 1904
	li %r0, 0
	stdu %r1, -1952(%r1)
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
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	addi %r1, %r1, 1952
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
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
