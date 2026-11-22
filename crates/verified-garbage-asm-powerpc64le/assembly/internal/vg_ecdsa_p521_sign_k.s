// The functions of `src/internal/vg_ecdsa_p521_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r4, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r4, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r4, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r4, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r4, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r4, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r4, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r4, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r5, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r5, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r5, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r5, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r5, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r5, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r5, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r5, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	ld %r4, 2440(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2448(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2440(%r3)
	ld %r4, 2448(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2456(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2448(%r3)
	ld %r4, 2456(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2464(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2456(%r3)
	ld %r4, 2464(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2472(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2464(%r3)
	ld %r4, 2472(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2480(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2472(%r3)
	ld %r4, 2480(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2488(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2480(%r3)
	ld %r4, 2488(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2496(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2488(%r3)
	ld %r4, 2496(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2504(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2496(%r3)
	ld %r4, 2504(%r3)
	rldicl %r4, %r4, 57, 7
	std %r4, 2504(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P521_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P521_FRAME_CONSTS}
	mtlr %r11
	li %r31, 153
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
	std %r4, 3232(%r3)
	li %r31, 72
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2296(%r4)
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
	li %r31, 72
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 928(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4672(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4673(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4674(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4675(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4676(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4677(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4678(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4679(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 72
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1000(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5248(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5249(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5250(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5251(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5252(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5253(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5254(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5255(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	lis %r11, -6878
	ori %r11, %r11, 61590
	stw %r11, 1072(%r3)
	lis %r11, -10344
	ori %r11, %r11, 41607
	stw %r11, 1076(%r3)
	lis %r11, 720
	ori %r11, %r11, 18515
	stw %r11, 1080(%r3)
	lis %r11, -9319
	ori %r11, %r11, 60402
	stw %r11, 1084(%r3)
	lis %r11, 17447
	ori %r11, %r11, 24542
	stw %r11, 1088(%r3)
	lis %r11, -24013
	ori %r11, %r11, 47269
	stw %r11, 1092(%r3)
	lis %r11, 4921
	ori %r11, %r11, 15950
	stw %r11, 1096(%r3)
	lis %r11, -11902
	ori %r11, %r11, 23456
	stw %r11, 1100(%r3)
	lis %r11, 28692
	ori %r11, %r11, 20147
	stw %r11, 1104(%r3)
	lis %r11, 32632
	ori %r11, %r11, 26015
	stw %r11, 1108(%r3)
	lis %r11, -22511
	ori %r11, %r11, 49528
	stw %r11, 1112(%r3)
	lis %r11, -9925
	ori %r11, %r11, 16258
	stw %r11, 1116(%r3)
	lis %r11, -28245
	ori %r11, %r11, 28933
	stw %r11, 1120(%r3)
	lis %r11, -32197
	ori %r11, %r11, 9736
	stw %r11, 1124(%r3)
	lis %r11, -28861
	ori %r11, %r11, 33104
	stw %r11, 1128(%r3)
	lis %r11, 12426
	ori %r11, %r11, 21220
	stw %r11, 1132(%r3)
	lis %r11, 0
	ori %r11, %r11, 458
	stw %r11, 1136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1140(%r3)
	lis %r11, 23473
	ori %r11, %r11, 10216
	stw %r11, 1144(%r3)
	lis %r11, 19213
	ori %r11, %r11, 63382
	stw %r11, 1148(%r3)
	lis %r11, 5520
	ori %r11, %r11, 27064
	stw %r11, 1152(%r3)
	lis %r11, -952
	ori %r11, %r11, 7397
	stw %r11, 1156(%r3)
	lis %r11, 474
	ori %r11, %r11, 22642
	stw %r11, 1160(%r3)
	lis %r11, -31569
	ori %r11, %r11, 17683
	stw %r11, 1164(%r3)
	lis %r11, -28710
	ori %r11, %r11, 4372
	stw %r11, 1168(%r3)
	lis %r11, 30605
	ori %r11, %r11, 899
	stw %r11, 1172(%r3)
	lis %r11, -2030
	ori %r11, %r11, 32282
	stw %r11, 1176(%r3)
	lis %r11, 14967
	ori %r11, %r11, 19519
	stw %r11, 1180(%r3)
	lis %r11, 1705
	ori %r11, %r11, 13611
	stw %r11, 1184(%r3)
	lis %r11, -26226
	ori %r11, %r11, 64078
	stw %r11, 1188(%r3)
	lis %r11, -272
	ori %r11, %r11, 18212
	stw %r11, 1192(%r3)
	lis %r11, -15124
	ori %r11, %r11, 34805
	stw %r11, 1196(%r3)
	lis %r11, -5390
	ori %r11, %r11, 36247
	stw %r11, 1200(%r3)
	lis %r11, -8030
	ori %r11, %r11, 25429
	stw %r11, 1204(%r3)
	lis %r11, 0
	ori %r11, %r11, 209
	stw %r11, 1208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1216(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1284(%r3)
	li %r31, 83
24:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -82
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
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
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
	addis %r8, %r8, ({VG_P521_COMB}
	addi %r8, %r8, ({VG_P521_COMB}
	li %r4, 9216
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
	vxor %v8, %v8, %v8
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
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v8, %v8, %v18, %v19
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	li %r4, 1504
	stxvd2x 32, %r3, %r4
	li %r4, 1520
	stxvd2x 33, %r3, %r4
	li %r4, 1536
	stxvd2x 34, %r3, %r4
	li %r4, 1552
	stxvd2x 35, %r3, %r4
	li %r4, 1568
	stxvd2x 36, %r3, %r4
	li %r4, 1584
	stxvd2x 37, %r3, %r4
	li %r4, 1600
	stxvd2x 38, %r3, %r4
	li %r4, 1616
	stxvd2x 39, %r3, %r4
	li %r4, 1632
	stxvd2x 40, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1648(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1652(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1656(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1660(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1664(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1668(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1672(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1676(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1680(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1684(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1688(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1692(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1696(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1700(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1708(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1712(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1716(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 1576(%r3)
	ld %r5, 1648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1576(%r3)
	ld %r4, 1584(%r3)
	ld %r5, 1656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 1592(%r3)
	ld %r5, 1664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 1600(%r3)
	ld %r5, 1672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 1608(%r3)
	ld %r5, 1680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 1616(%r3)
	ld %r5, 1688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 1624(%r3)
	ld %r5, 1696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1624(%r3)
	ld %r4, 1632(%r3)
	ld %r5, 1704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1632(%r3)
	ld %r4, 1640(%r3)
	ld %r5, 1712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1640(%r3)
	ld %r4, 1648(%r3)
	ld %r5, 280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1648(%r3)
	ld %r4, 1656(%r3)
	ld %r5, 288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1656(%r3)
	ld %r4, 1664(%r3)
	ld %r5, 296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1664(%r3)
	ld %r4, 1672(%r3)
	ld %r5, 304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1672(%r3)
	ld %r4, 1680(%r3)
	ld %r5, 312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1680(%r3)
	ld %r4, 1688(%r3)
	ld %r5, 320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1688(%r3)
	ld %r4, 1696(%r3)
	ld %r5, 328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1696(%r3)
	ld %r4, 1704(%r3)
	ld %r5, 336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1704(%r3)
	ld %r4, 1712(%r3)
	ld %r5, 344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1712(%r3)
	li %r4, 1288
	li %r5, 280
	li %r6, 1576
	bl {vg_p521_sub_mod_p}
	addi %r6, %r31, -82
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
	ld %r4, 1576(%r3)
	ld %r5, 1288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1576(%r3)
	ld %r4, 1584(%r3)
	ld %r5, 1296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 1592(%r3)
	ld %r5, 1304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 1600(%r3)
	ld %r5, 1312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 1608(%r3)
	ld %r5, 1320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 1616(%r3)
	ld %r5, 1328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 1624(%r3)
	ld %r5, 1336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1624(%r3)
	ld %r4, 1632(%r3)
	ld %r5, 1344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1632(%r3)
	ld %r4, 1640(%r3)
	ld %r5, 1352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1640(%r3)
	li %r4, 1720
	li %r5, 1072
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1144
	li %r6, 1576
	bl {vg_p521_mul_mod_p}
	li %r4, 1864
	li %r5, 1216
	li %r6, 1648
	bl {vg_p521_mul_mod_p}
	li %r4, 1936
	li %r5, 1072
	li %r6, 1144
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 1504
	li %r6, 1576
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 1720
	li %r6, 1792
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_sub_mod_p}
	li %r4, 2008
	li %r5, 1072
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 1504
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_mul_mod_p}
	li %r4, 2080
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_sub_mod_p}
	li %r4, 2080
	li %r5, 1144
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1576
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 496
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 568
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 568
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_sub_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1792
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 2080
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1936
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1288
	li %r6, 1720
	bl {vg_p521_sub_mod_p}
	li %r4, 1720
	li %r5, 1936
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 2080
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1432
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	ld %r4, 1288(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1088(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1096(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1104(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1112(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1120(%r3)
	ld %r4, 1344(%r3)
	std %r4, 1128(%r3)
	ld %r4, 1352(%r3)
	std %r4, 1136(%r3)
	ld %r4, 1360(%r3)
	std %r4, 1144(%r3)
	ld %r4, 1368(%r3)
	std %r4, 1152(%r3)
	ld %r4, 1376(%r3)
	std %r4, 1160(%r3)
	ld %r4, 1384(%r3)
	std %r4, 1168(%r3)
	ld %r4, 1392(%r3)
	std %r4, 1176(%r3)
	ld %r4, 1400(%r3)
	std %r4, 1184(%r3)
	ld %r4, 1408(%r3)
	std %r4, 1192(%r3)
	ld %r4, 1416(%r3)
	std %r4, 1200(%r3)
	ld %r4, 1424(%r3)
	std %r4, 1208(%r3)
	ld %r4, 1432(%r3)
	std %r4, 1216(%r3)
	ld %r4, 1440(%r3)
	std %r4, 1224(%r3)
	ld %r4, 1448(%r3)
	std %r4, 1232(%r3)
	ld %r4, 1456(%r3)
	std %r4, 1240(%r3)
	ld %r4, 1464(%r3)
	std %r4, 1248(%r3)
	ld %r4, 1472(%r3)
	std %r4, 1256(%r3)
	ld %r4, 1480(%r3)
	std %r4, 1264(%r3)
	ld %r4, 1488(%r3)
	std %r4, 1272(%r3)
	ld %r4, 1496(%r3)
	std %r4, 1280(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	bl {vg_p521_inv_mod_p}
	li %r4, 2512
	li %r5, 1072
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2584
	li %r5, 2512
	li %r6, 352
	bl {vg_p521_mul_mod_p}
	li %r4, 2656
	li %r5, 2584
	li %r6, 280
	bl {vg_p521_add_mod_n}
	li %r4, 2728
	li %r5, 2296
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2368(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2372(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2376(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2380(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2384(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2388(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2392(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2396(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2400(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2404(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2408(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2412(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2416(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2420(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2424(%r3)
	lwz %r8, 192(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2428(%r3)
	lwz %r8, 196(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2432(%r3)
	lwz %r8, 200(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2436(%r3)
	lwz %r8, 204(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
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
	ld %r4, 2432(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2296(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2300(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2304(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2308(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2312(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2316(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2320(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2324(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2328(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2332(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2336(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2340(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2344(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2348(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2352(%r3)
	lwz %r8, 192(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2356(%r3)
	lwz %r8, 196(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2360(%r3)
	lwz %r8, 200(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2364(%r3)
	lwz %r8, 204(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2296(%r3)
	ld %r4, 2304(%r3)
	or %r5, %r5, %r4
	ld %r4, 2312(%r3)
	or %r5, %r5, %r4
	ld %r4, 2320(%r3)
	or %r5, %r5, %r4
	ld %r4, 2328(%r3)
	or %r5, %r5, %r4
	ld %r4, 2336(%r3)
	or %r5, %r5, %r4
	ld %r4, 2344(%r3)
	or %r5, %r5, %r4
	ld %r4, 2352(%r3)
	or %r5, %r5, %r4
	ld %r4, 2360(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r5, 2656(%r3)
	ld %r4, 2664(%r3)
	or %r5, %r5, %r4
	ld %r4, 2672(%r3)
	or %r5, %r5, %r4
	ld %r4, 2680(%r3)
	or %r5, %r5, %r4
	ld %r4, 2688(%r3)
	or %r5, %r5, %r4
	ld %r4, 2696(%r3)
	or %r5, %r5, %r4
	ld %r4, 2704(%r3)
	or %r5, %r5, %r4
	ld %r4, 2712(%r3)
	or %r5, %r5, %r4
	ld %r4, 2720(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	bl {vg_p521_inv_mod_n}
	li %r4, 2800
	li %r5, 2656
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 2872
	li %r5, 2368
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 2944
	li %r5, 2440
	li %r6, 784
	bl {vg_p521_mul_mod_n}
	li %r4, 3016
	li %r5, 2800
	li %r6, 2872
	bl {vg_p521_mul_mod_n}
	li %r4, 3016
	li %r5, 3016
	li %r6, 2944
	bl {vg_p521_add_mod_n}
	li %r4, 3088
	li %r5, 2152
	li %r6, 3016
	bl {vg_p521_mul_mod_n}
	li %r4, 3160
	li %r5, 3088
	li %r6, 352
	bl {vg_p521_mul_mod_n}
	ld %r5, 3160(%r3)
	ld %r4, 3168(%r3)
	or %r5, %r5, %r4
	ld %r4, 3176(%r3)
	or %r5, %r5, %r4
	ld %r4, 3184(%r3)
	or %r5, %r5, %r4
	ld %r4, 3192(%r3)
	or %r5, %r5, %r4
	ld %r4, 3200(%r3)
	or %r5, %r5, %r4
	ld %r4, 3208(%r3)
	or %r5, %r5, %r4
	ld %r4, 3216(%r3)
	or %r5, %r5, %r4
	ld %r4, 3224(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	ld %r4, 2656(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r14, %r6
	ld %r4, 2664(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r14, %r6
	ld %r4, 2672(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r14, %r6
	ld %r4, 2680(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r14, %r6
	ld %r4, 2688(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r14, %r6
	ld %r4, 2696(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r14, %r6
	ld %r4, 2704(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r14, %r6
	ld %r4, 2712(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r14, %r6
	ld %r4, 2720(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r14)
	stb %r4, 1(%r14)
	ld %r4, 3160(%r3)
	and %r4, %r4, %r10
	li %r6, 124
	stdbrx %r4, %r14, %r6
	ld %r4, 3168(%r3)
	and %r4, %r4, %r10
	li %r6, 116
	stdbrx %r4, %r14, %r6
	ld %r4, 3176(%r3)
	and %r4, %r4, %r10
	li %r6, 108
	stdbrx %r4, %r14, %r6
	ld %r4, 3184(%r3)
	and %r4, %r4, %r10
	li %r6, 100
	stdbrx %r4, %r14, %r6
	ld %r4, 3192(%r3)
	and %r4, %r4, %r10
	li %r6, 92
	stdbrx %r4, %r14, %r6
	ld %r4, 3200(%r3)
	and %r4, %r4, %r10
	li %r6, 84
	stdbrx %r4, %r14, %r6
	ld %r4, 3208(%r3)
	and %r4, %r4, %r10
	li %r6, 76
	stdbrx %r4, %r14, %r6
	ld %r4, 3216(%r3)
	and %r4, %r4, %r10
	li %r6, 68
	stdbrx %r4, %r14, %r6
	ld %r4, 3224(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 66(%r14)
	stb %r4, 67(%r14)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
