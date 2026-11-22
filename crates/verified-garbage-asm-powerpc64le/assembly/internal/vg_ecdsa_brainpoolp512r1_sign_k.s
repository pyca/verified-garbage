// The functions of `src/internal/vg_ecdsa_brainpoolp512r1_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r4, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r4, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r5, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r5, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r5, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 2232(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP512R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 136
20:
	addi %r31, %r31, -1
	rldicr %r8, %r31, 3, 60
	add %r9, %r4, %r8
	ld %r11, 0(%r9)
	add %r9, %r3, %r8
	std %r11, 64(%r9)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2880(%r3)
	li %r31, 64
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2048(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r31, 64
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 832(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4608(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4609(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4610(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4611(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4612(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4613(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4614(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4615(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 64
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 896(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5120(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5121(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5122(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5123(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5124(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5125(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5126(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5127(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	lis %r11, 723
	ori %r11, %r11, 24749
	stw %r11, 960(%r3)
	lis %r11, 10122
	ori %r11, %r11, 26908
	stw %r11, 964(%r3)
	lis %r11, -20070
	ori %r11, %r11, 47708
	stw %r11, 968(%r3)
	lis %r11, -1963
	ori %r11, %r11, 63333
	stw %r11, 972(%r3)
	lis %r11, -16914
	ori %r11, %r11, 32431
	stw %r11, 976(%r3)
	lis %r11, 9804
	ori %r11, %r11, 22524
	stw %r11, 980(%r3)
	lis %r11, 25470
	ori %r11, %r11, 20273
	stw %r11, 984(%r3)
	lis %r11, -4204
	ori %r11, %r11, 4032
	stw %r11, 988(%r3)
	lis %r11, -2303
	ori %r11, %r11, 60103
	stw %r11, 992(%r3)
	lis %r11, 21414
	ori %r11, %r11, 61066
	stw %r11, 996(%r3)
	lis %r11, 23664
	ori %r11, %r11, 51386
	stw %r11, 1000(%r3)
	lis %r11, -8252
	ori %r11, %r11, 27876
	stw %r11, 1004(%r3)
	lis %r11, 2097
	ori %r11, %r11, 33648
	stw %r11, 1008(%r3)
	lis %r11, 31331
	ori %r11, %r11, 9370
	stw %r11, 1012(%r3)
	lis %r11, -357
	ori %r11, %r11, 24707
	stw %r11, 1016(%r3)
	lis %r11, 23585
	ori %r11, %r11, 14231
	stw %r11, 1020(%r3)
	lis %r11, 7036
	ori %r11, %r11, 31196
	stw %r11, 1024(%r3)
	lis %r11, 7774
	ori %r11, %r11, 10383
	stw %r11, 1028(%r3)
	lis %r11, -1639
	ori %r11, %r11, 55885
	stw %r11, 1032(%r3)
	lis %r11, 22852
	ori %r11, %r11, 40253
	stw %r11, 1036(%r3)
	lis %r11, -30974
	ori %r11, %r11, 588
	stw %r11, 1040(%r3)
	lis %r11, 9380
	ori %r11, %r11, 54870
	stw %r11, 1044(%r3)
	lis %r11, -13535
	ori %r11, %r11, 51918
	stw %r11, 1048(%r3)
	lis %r11, -28946
	ori %r11, %r11, 485
	stw %r11, 1052(%r3)
	lis %r11, 11387
	ori %r11, %r11, 53737
	stw %r11, 1056(%r3)
	lis %r11, -6686
	ori %r11, %r11, 7322
	stw %r11, 1060(%r3)
	lis %r11, -20504
	ori %r11, %r11, 35845
	stw %r11, 1064(%r3)
	lis %r11, 26060
	ori %r11, %r11, 61749
	stw %r11, 1068(%r3)
	lis %r11, -20690
	ori %r11, %r11, 39269
	stw %r11, 1072(%r3)
	lis %r11, 30292
	ori %r11, %r11, 49447
	stw %r11, 1076(%r3)
	lis %r11, 24172
	ori %r11, %r11, 10673
	stw %r11, 1080(%r3)
	lis %r11, 21547
	ori %r11, %r11, 40998
	stw %r11, 1084(%r3)
	lis %r11, -22587
	ori %r11, %r11, 46861
	stw %r11, 1088(%r3)
	lis %r11, -10411
	ori %r11, %r11, 40873
	stw %r11, 1092(%r3)
	lis %r11, -11651
	ori %r11, %r11, 14714
	stw %r11, 1096(%r3)
	lis %r11, -10370
	ori %r11, %r11, 208
	stw %r11, 1100(%r3)
	lis %r11, 6492
	ori %r11, %r11, 32537
	stw %r11, 1104(%r3)
	lis %r11, 20786
	ori %r11, %r11, 24277
	stw %r11, 1108(%r3)
	lis %r11, 25657
	ori %r11, %r11, 38845
	stw %r11, 1112(%r3)
	lis %r11, -32078
	ori %r11, %r11, 25855
	stw %r11, 1116(%r3)
	lis %r11, -28724
	ori %r11, %r11, 63374
	stw %r11, 1120(%r3)
	lis %r11, 10652
	ori %r11, %r11, 25397
	stw %r11, 1124(%r3)
	lis %r11, 19510
	ori %r11, %r11, 11761
	stw %r11, 1128(%r3)
	lis %r11, 13519
	ori %r11, %r11, 29260
	stw %r11, 1132(%r3)
	lis %r11, -13258
	ori %r11, %r11, 1016
	stw %r11, 1136(%r3)
	lis %r11, -16341
	ori %r11, %r11, 6481
	stw %r11, 1140(%r3)
	lis %r11, 9238
	ori %r11, %r11, 15220
	stw %r11, 1144(%r3)
	lis %r11, 21794
	ori %r11, %r11, 25159
	stw %r11, 1148(%r3)
	li %r31, 74
24:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -73
	cmpldi %cr0, %r6, 0
	beq %cr0, 25f
	li %r9, 0
	add %r9, %r9, %r9
	lbz %r5, 4102(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4101(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4100(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4099(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	b 26f
25:
	li %r9, 0
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
26:
	addi %r9, %r9, -64
	rldicl %r4, %r9, 1, 63
	li %r5, 0
	subf %r4, %r4, %r5
	xor %r9, %r9, %r4
	subf %r9, %r4, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_BRAINPOOLP512R1_COMB}
	addi %r8, %r8, ({VG_BRAINPOOLP512R1_COMB}
	li %r4, 8192
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	li %r7, 1
27:
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	mtvsrd 51, %r10
	vspltw %v19, %v19, 0
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v0, %v0, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v1, %v1, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v2, %v2, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v3, %v3, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v4, %v4, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v5, %v5, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v6, %v6, %v18, %v19
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v7, %v7, %v18, %v19
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	li %r4, 1344
	stxvd2x 32, %r3, %r4
	li %r4, 1360
	stxvd2x 33, %r3, %r4
	li %r4, 1376
	stxvd2x 34, %r3, %r4
	li %r4, 1392
	stxvd2x 35, %r3, %r4
	li %r4, 1408
	stxvd2x 36, %r3, %r4
	li %r4, 1424
	stxvd2x 37, %r3, %r4
	li %r4, 1440
	stxvd2x 38, %r3, %r4
	li %r4, 1456
	stxvd2x 39, %r3, %r4
	lis %r11, -22587
	ori %r11, %r11, 46861
	stw %r11, 1472(%r3)
	lis %r11, -10411
	ori %r11, %r11, 40873
	stw %r11, 1476(%r3)
	lis %r11, -11651
	ori %r11, %r11, 14714
	stw %r11, 1480(%r3)
	lis %r11, -10370
	ori %r11, %r11, 208
	stw %r11, 1484(%r3)
	lis %r11, 6492
	ori %r11, %r11, 32537
	stw %r11, 1488(%r3)
	lis %r11, 20786
	ori %r11, %r11, 24277
	stw %r11, 1492(%r3)
	lis %r11, 25657
	ori %r11, %r11, 38845
	stw %r11, 1496(%r3)
	lis %r11, -32078
	ori %r11, %r11, 25855
	stw %r11, 1500(%r3)
	lis %r11, -28724
	ori %r11, %r11, 63374
	stw %r11, 1504(%r3)
	lis %r11, 10652
	ori %r11, %r11, 25397
	stw %r11, 1508(%r3)
	lis %r11, 19510
	ori %r11, %r11, 11761
	stw %r11, 1512(%r3)
	lis %r11, 13519
	ori %r11, %r11, 29260
	stw %r11, 1516(%r3)
	lis %r11, -13258
	ori %r11, %r11, 1016
	stw %r11, 1520(%r3)
	lis %r11, -16341
	ori %r11, %r11, 6481
	stw %r11, 1524(%r3)
	lis %r11, 9238
	ori %r11, %r11, 15220
	stw %r11, 1528(%r3)
	lis %r11, 21794
	ori %r11, %r11, 25159
	stw %r11, 1532(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 1408(%r3)
	ld %r5, 1472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1408(%r3)
	ld %r4, 1416(%r3)
	ld %r5, 1480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1416(%r3)
	ld %r4, 1424(%r3)
	ld %r5, 1488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1424(%r3)
	ld %r4, 1432(%r3)
	ld %r5, 1496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1432(%r3)
	ld %r4, 1440(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1440(%r3)
	ld %r4, 1448(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1448(%r3)
	ld %r4, 1456(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	ld %r4, 1472(%r3)
	ld %r5, 256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r4, 1480(%r3)
	ld %r5, 264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1480(%r3)
	ld %r4, 1488(%r3)
	ld %r5, 272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1488(%r3)
	ld %r4, 1496(%r3)
	ld %r5, 280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1496(%r3)
	ld %r4, 1504(%r3)
	ld %r5, 288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1504(%r3)
	ld %r4, 1512(%r3)
	ld %r5, 296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1512(%r3)
	ld %r4, 1520(%r3)
	ld %r5, 304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1520(%r3)
	ld %r4, 1528(%r3)
	ld %r5, 312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1528(%r3)
	li %r4, 1152
	li %r5, 256
	li %r6, 1408
	bl {vg_brainpoolp512r1_sub_mod_p}
	addi %r6, %r31, -73
	cmpldi %cr0, %r6, 0
	beq %cr0, 28f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	addi %r10, %r4, -1
	b 29f
28:
	li %r10, 0
	addi %r10, %r10, -1
29:
	ld %r4, 1408(%r3)
	ld %r5, 1152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1408(%r3)
	ld %r4, 1416(%r3)
	ld %r5, 1160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1416(%r3)
	ld %r4, 1424(%r3)
	ld %r5, 1168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1424(%r3)
	ld %r4, 1432(%r3)
	ld %r5, 1176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1432(%r3)
	ld %r4, 1440(%r3)
	ld %r5, 1184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1440(%r3)
	ld %r4, 1448(%r3)
	ld %r5, 1192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1448(%r3)
	ld %r4, 1456(%r3)
	ld %r5, 1200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	li %r4, 1536
	li %r5, 960
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1024
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1664
	li %r5, 1088
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1728
	li %r5, 960
	li %r6, 1024
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1344
	li %r6, 1408
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1536
	li %r6, 1600
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1792
	li %r5, 960
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1344
	li %r6, 1472
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1856
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1856
	li %r5, 1024
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1152
	li %r5, 1408
	li %r6, 1472
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1152
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1280
	li %r5, 448
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 512
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1152
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1152
	li %r5, 1600
	li %r6, 1280
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1280
	li %r5, 1600
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1216
	li %r5, 1152
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 512
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1600
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1856
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1728
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1152
	li %r6, 1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1536
	li %r5, 1728
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1856
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1280
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	ld %r4, 1152(%r3)
	std %r4, 960(%r3)
	ld %r4, 1160(%r3)
	std %r4, 968(%r3)
	ld %r4, 1168(%r3)
	std %r4, 976(%r3)
	ld %r4, 1176(%r3)
	std %r4, 984(%r3)
	ld %r4, 1184(%r3)
	std %r4, 992(%r3)
	ld %r4, 1192(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1200(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1208(%r3)
	std %r4, 1016(%r3)
	ld %r4, 1216(%r3)
	std %r4, 1024(%r3)
	ld %r4, 1224(%r3)
	std %r4, 1032(%r3)
	ld %r4, 1232(%r3)
	std %r4, 1040(%r3)
	ld %r4, 1240(%r3)
	std %r4, 1048(%r3)
	ld %r4, 1248(%r3)
	std %r4, 1056(%r3)
	ld %r4, 1256(%r3)
	std %r4, 1064(%r3)
	ld %r4, 1264(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1272(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1280(%r3)
	std %r4, 1088(%r3)
	ld %r4, 1288(%r3)
	std %r4, 1096(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1104(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1112(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1120(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1128(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1136(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1144(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	bl {vg_brainpoolp512r1_inv_mod_p}
	li %r4, 2240
	li %r5, 960
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2304
	li %r5, 2240
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2368
	li %r5, 2304
	li %r6, 256
	bl {vg_brainpoolp512r1_add_mod_n}
	li %r4, 2432
	li %r5, 2048
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2112(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2116(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2120(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2124(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2128(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2132(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2136(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2140(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2144(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2148(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2152(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2156(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2160(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2164(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2168(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2172(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2112(%r3)
	ld %r4, 2120(%r3)
	or %r5, %r5, %r4
	ld %r4, 2128(%r3)
	or %r5, %r5, %r4
	ld %r4, 2136(%r3)
	or %r5, %r5, %r4
	ld %r4, 2144(%r3)
	or %r5, %r5, %r4
	ld %r4, 2152(%r3)
	or %r5, %r5, %r4
	ld %r4, 2160(%r3)
	or %r5, %r5, %r4
	ld %r4, 2168(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2048(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2052(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2056(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2060(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2064(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2068(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2072(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2076(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2080(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2084(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2088(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2092(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2096(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2100(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2104(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2108(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2048(%r3)
	ld %r4, 2056(%r3)
	or %r5, %r5, %r4
	ld %r4, 2064(%r3)
	or %r5, %r5, %r4
	ld %r4, 2072(%r3)
	or %r5, %r5, %r4
	ld %r4, 2080(%r3)
	or %r5, %r5, %r4
	ld %r4, 2088(%r3)
	or %r5, %r5, %r4
	ld %r4, 2096(%r3)
	or %r5, %r5, %r4
	ld %r4, 2104(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r5, 2368(%r3)
	ld %r4, 2376(%r3)
	or %r5, %r5, %r4
	ld %r4, 2384(%r3)
	or %r5, %r5, %r4
	ld %r4, 2392(%r3)
	or %r5, %r5, %r4
	ld %r4, 2400(%r3)
	or %r5, %r5, %r4
	ld %r4, 2408(%r3)
	or %r5, %r5, %r4
	ld %r4, 2416(%r3)
	or %r5, %r5, %r4
	ld %r4, 2424(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	bl {vg_brainpoolp512r1_inv_mod_n}
	li %r4, 2496
	li %r5, 2368
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2560
	li %r5, 2112
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2624
	li %r5, 2176
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2688
	li %r5, 2496
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2688
	li %r5, 2688
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_n}
	li %r4, 2752
	li %r5, 1920
	li %r6, 2688
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2816
	li %r5, 2752
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_n}
	ld %r5, 2816(%r3)
	ld %r4, 2824(%r3)
	or %r5, %r5, %r4
	ld %r4, 2832(%r3)
	or %r5, %r5, %r4
	ld %r4, 2840(%r3)
	or %r5, %r5, %r4
	ld %r4, 2848(%r3)
	or %r5, %r5, %r4
	ld %r4, 2856(%r3)
	or %r5, %r5, %r4
	ld %r4, 2864(%r3)
	or %r5, %r5, %r4
	ld %r4, 2872(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 2368(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 2376(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 2384(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 2392(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 2400(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 2408(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 2416(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 2424(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 2816(%r3)
	and %r4, %r4, %r10
	li %r6, 120
	stdbrx %r4, %r14, %r6
	ld %r4, 2824(%r3)
	and %r4, %r4, %r10
	li %r6, 112
	stdbrx %r4, %r14, %r6
	ld %r4, 2832(%r3)
	and %r4, %r4, %r10
	li %r6, 104
	stdbrx %r4, %r14, %r6
	ld %r4, 2840(%r3)
	and %r4, %r4, %r10
	li %r6, 96
	stdbrx %r4, %r14, %r6
	ld %r4, 2848(%r3)
	and %r4, %r4, %r10
	li %r6, 88
	stdbrx %r4, %r14, %r6
	ld %r4, 2856(%r3)
	and %r4, %r4, %r10
	li %r6, 80
	stdbrx %r4, %r14, %r6
	ld %r4, 2864(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 2872(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
