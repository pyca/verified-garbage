// The functions of `src/pbkdf2_sha256.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256:
	stdu %r1, -1632(%r1)
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
	addi %r3, %r21, 880
	addi %r4, %r21, 976
	bl {vg_hmac_sha256_init_core}
	li %r12, 1
	li %r11, 1232
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 880(%r21)
	stw %r8, 1072(%r21)
	lwz %r8, 884(%r21)
	stw %r8, 1076(%r21)
	lwz %r8, 888(%r21)
	stw %r8, 1080(%r21)
	lwz %r8, 892(%r21)
	stw %r8, 1084(%r21)
	lwz %r8, 896(%r21)
	stw %r8, 1088(%r21)
	lwz %r8, 900(%r21)
	stw %r8, 1092(%r21)
	lwz %r8, 904(%r21)
	stw %r8, 1096(%r21)
	lwz %r8, 908(%r21)
	stw %r8, 1100(%r21)
	lwz %r8, 912(%r21)
	stw %r8, 1104(%r21)
	lwz %r8, 916(%r21)
	stw %r8, 1108(%r21)
	lwz %r8, 920(%r21)
	stw %r8, 1112(%r21)
	lwz %r8, 924(%r21)
	stw %r8, 1116(%r21)
	lwz %r8, 928(%r21)
	stw %r8, 1120(%r21)
	lwz %r8, 932(%r21)
	stw %r8, 1124(%r21)
	lwz %r8, 936(%r21)
	stw %r8, 1128(%r21)
	lwz %r8, 940(%r21)
	stw %r8, 1132(%r21)
	lwz %r8, 944(%r21)
	stw %r8, 1136(%r21)
	lwz %r8, 948(%r21)
	stw %r8, 1140(%r21)
	lwz %r8, 952(%r21)
	stw %r8, 1144(%r21)
	lwz %r8, 956(%r21)
	stw %r8, 1148(%r21)
	lwz %r8, 960(%r21)
	stw %r8, 1152(%r21)
	lwz %r8, 964(%r21)
	stw %r8, 1156(%r21)
	lwz %r8, 968(%r21)
	stw %r8, 1160(%r21)
	lwz %r8, 972(%r21)
	stw %r8, 1164(%r21)
	addi %r3, %r21, 1072
	li %r4, 64
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_sha256_update_scratch}
	addi %r3, %r21, 1072
	addi %r4, %r20, 64
	addi %r5, %r21, 1232
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_sha256_update_scratch}
	addi %r3, %r21, 1072
	addi %r4, %r21, 976
	addi %r5, %r20, 68
	addi %r6, %r21, 1168
	addi %r7, %r21, 48
	bl {vg_hmac_sha256_finalize_scratch}
	lwz %r8, 1168(%r21)
	stw %r8, 1200(%r21)
	lwz %r8, 1172(%r21)
	stw %r8, 1204(%r21)
	lwz %r8, 1176(%r21)
	stw %r8, 1208(%r21)
	lwz %r8, 1180(%r21)
	stw %r8, 1212(%r21)
	lwz %r8, 1184(%r21)
	stw %r8, 1216(%r21)
	lwz %r8, 1188(%r21)
	stw %r8, 1220(%r21)
	lwz %r8, 1192(%r21)
	stw %r8, 1224(%r21)
	lwz %r8, 1196(%r21)
	stw %r8, 1228(%r21)
	addi %r3, %r21, 880
	addi %r4, %r21, 1168
	addi %r5, %r22, -1
	addi %r6, %r21, 1200
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_sha256_iterate}
	addi %r12, %r24, -32
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 32
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 1200(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 1232
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
	addi %r1, %r1, 1632
	li %r0, 0
	stdu %r1, -2640(%r1)
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
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	std %r0, 2192(%r12)
	std %r0, 2200(%r12)
	std %r0, 2208(%r12)
	std %r0, 2216(%r12)
	std %r0, 2224(%r12)
	std %r0, 2232(%r12)
	std %r0, 2240(%r12)
	std %r0, 2248(%r12)
	std %r0, 2256(%r12)
	std %r0, 2264(%r12)
	std %r0, 2272(%r12)
	std %r0, 2280(%r12)
	std %r0, 2288(%r12)
	std %r0, 2296(%r12)
	std %r0, 2304(%r12)
	std %r0, 2312(%r12)
	std %r0, 2320(%r12)
	std %r0, 2328(%r12)
	std %r0, 2336(%r12)
	std %r0, 2344(%r12)
	std %r0, 2352(%r12)
	std %r0, 2360(%r12)
	std %r0, 2368(%r12)
	std %r0, 2376(%r12)
	std %r0, 2384(%r12)
	std %r0, 2392(%r12)
	std %r0, 2400(%r12)
	std %r0, 2408(%r12)
	std %r0, 2416(%r12)
	std %r0, 2424(%r12)
	std %r0, 2432(%r12)
	std %r0, 2440(%r12)
	std %r0, 2448(%r12)
	std %r0, 2456(%r12)
	std %r0, 2464(%r12)
	std %r0, 2472(%r12)
	std %r0, 2480(%r12)
	std %r0, 2488(%r12)
	std %r0, 2496(%r12)
	std %r0, 2504(%r12)
	std %r0, 2512(%r12)
	std %r0, 2520(%r12)
	std %r0, 2528(%r12)
	std %r0, 2536(%r12)
	std %r0, 2544(%r12)
	std %r0, 2552(%r12)
	std %r0, 2560(%r12)
	std %r0, 2568(%r12)
	std %r0, 2576(%r12)
	std %r0, 2584(%r12)
	std %r0, 2592(%r12)
	std %r0, 2600(%r12)
	addi %r1, %r1, 2640
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
