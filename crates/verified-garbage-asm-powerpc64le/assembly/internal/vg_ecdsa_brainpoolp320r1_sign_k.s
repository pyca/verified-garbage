// The functions of `src/internal/vg_ecdsa_brainpoolp320r1_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp320r1_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1304(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1312(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1320(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1328(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1336(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1344(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1352(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1360(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1368(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1376(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 1384(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1392(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1400(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1408(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1416(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	addi %r4, %r4, ({VG_BRAINPOOLP320R1_FRAME_CONSTS}
	mtlr %r11
	li %r31, 17
	addi %r9, %r3, 0
20:
	addi %r31, %r31, -1
	ld %r11, 0(%r4)
	std %r11, 64(%r9)
	ld %r11, 8(%r4)
	std %r11, 72(%r9)
	ld %r11, 16(%r4)
	std %r11, 80(%r9)
	ld %r11, 24(%r4)
	std %r11, 88(%r9)
	ld %r11, 32(%r4)
	std %r11, 96(%r9)
	addi %r4, %r4, 40
	addi %r9, %r9, 40
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1824(%r3)
	li %r31, 40
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1304(%r4)
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
	li %r31, 40
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 544(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4416(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4417(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4418(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4419(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4420(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4421(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4422(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4423(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 40
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 584(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4736(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4737(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4738(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4739(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4740(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4741(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4742(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4743(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 384(%r3)
	std %r4, 3272(%r3)
	ld %r4, 392(%r3)
	std %r4, 3280(%r3)
	ld %r4, 400(%r3)
	std %r4, 3288(%r3)
	ld %r4, 408(%r3)
	std %r4, 3296(%r3)
	ld %r4, 416(%r3)
	std %r4, 3304(%r3)
	ld %r4, 424(%r3)
	std %r4, 3312(%r3)
	ld %r4, 432(%r3)
	std %r4, 3320(%r3)
	ld %r4, 440(%r3)
	std %r4, 3328(%r3)
	ld %r4, 448(%r3)
	std %r4, 3336(%r3)
	ld %r4, 456(%r3)
	std %r4, 3344(%r3)
	ld %r4, 264(%r3)
	std %r4, 3352(%r3)
	ld %r4, 272(%r3)
	std %r4, 3360(%r3)
	ld %r4, 280(%r3)
	std %r4, 3368(%r3)
	ld %r4, 288(%r3)
	std %r4, 3376(%r3)
	ld %r4, 296(%r3)
	std %r4, 3384(%r3)
	ld %r4, 304(%r3)
	std %r4, 3392(%r3)
	ld %r4, 312(%r3)
	std %r4, 3400(%r3)
	ld %r4, 320(%r3)
	std %r4, 3408(%r3)
	ld %r4, 328(%r3)
	std %r4, 3416(%r3)
	ld %r4, 336(%r3)
	std %r4, 3424(%r3)
	ld %r4, 344(%r3)
	std %r4, 3432(%r3)
	ld %r4, 352(%r3)
	std %r4, 3440(%r3)
	ld %r4, 360(%r3)
	std %r4, 3448(%r3)
	ld %r4, 368(%r3)
	std %r4, 3456(%r3)
	ld %r4, 376(%r3)
	std %r4, 3464(%r3)
	lis %r11, 2198
	ori %r11, %r11, 21888
	stw %r11, 624(%r3)
	lis %r11, 19873
	ori %r11, %r11, 41135
	stw %r11, 628(%r3)
	lis %r11, 25931
	ori %r11, %r11, 28825
	stw %r11, 632(%r3)
	lis %r11, 25670
	ori %r11, %r11, 63964
	stw %r11, 636(%r3)
	lis %r11, 29184
	ori %r11, %r11, 28887
	stw %r11, 640(%r3)
	lis %r11, -20072
	ori %r11, %r11, 37574
	stw %r11, 644(%r3)
	lis %r11, -13122
	ori %r11, %r11, 17146
	stw %r11, 648(%r3)
	lis %r11, -8207
	ori %r11, %r11, 43243
	stw %r11, 652(%r3)
	lis %r11, -27152
	ori %r11, %r11, 7190
	stw %r11, 656(%r3)
	lis %r11, 17621
	ori %r11, %r11, 41073
	stw %r11, 660(%r3)
	lis %r11, -2775
	ori %r11, %r11, 20243
	stw %r11, 664(%r3)
	lis %r11, 15453
	ori %r11, %r11, 28964
	stw %r11, 668(%r3)
	lis %r11, 31571
	ori %r11, %r11, 31306
	stw %r11, 672(%r3)
	lis %r11, 13894
	ori %r11, %r11, 45918
	stw %r11, 676(%r3)
	lis %r11, -9190
	ori %r11, %r11, 17111
	stw %r11, 680(%r3)
	lis %r11, -29556
	ori %r11, %r11, 35437
	stw %r11, 684(%r3)
	lis %r11, 2155
	ori %r11, %r11, 55457
	stw %r11, 688(%r3)
	lis %r11, -29600
	ori %r11, %r11, 44970
	stw %r11, 692(%r3)
	lis %r11, 31933
	ori %r11, %r11, 23878
	stw %r11, 696(%r3)
	lis %r11, -19149
	ori %r11, %r11, 48074
	stw %r11, 700(%r3)
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 704(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 708(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 712(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 716(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 720(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 724(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 728(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 732(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 736(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 740(%r3)
	li %r31, 46
24:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -45
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
	addis %r8, %r8, ({VG_BRAINPOOLP320R1_COMB}
	addi %r8, %r8, ({VG_BRAINPOOLP320R1_COMB}
	li %r4, 5120
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	li %r4, 3272
	stxvd2x 32, %r3, %r4
	li %r4, 3288
	stxvd2x 33, %r3, %r4
	li %r4, 3304
	stxvd2x 34, %r3, %r4
	li %r4, 3320
	stxvd2x 35, %r3, %r4
	li %r4, 3336
	stxvd2x 36, %r3, %r4
	lis %r11, 3660
	ori %r11, %r11, 53721
	stw %r11, 3352(%r3)
	lis %r11, 811
	ori %r11, %r11, 60750
	stw %r11, 3356(%r3)
	lis %r11, -30868
	ori %r11, %r11, 5079
	stw %r11, 3360(%r3)
	lis %r11, -20371
	ori %r11, %r11, 17939
	stw %r11, 3364(%r3)
	lis %r11, 2315
	ori %r11, %r11, 61968
	stw %r11, 3368(%r3)
	lis %r11, 1648
	ori %r11, %r11, 12377
	stw %r11, 3372(%r3)
	lis %r11, 11774
	ori %r11, %r11, 8090
	stw %r11, 3376(%r3)
	lis %r11, 7875
	ori %r11, %r11, 34721
	stw %r11, 3380(%r3)
	lis %r11, -14013
	ori %r11, %r11, 45128
	stw %r11, 3384(%r3)
	lis %r11, 11425
	ori %r11, %r11, 47327
	stw %r11, 3388(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3312(%r3)
	ld %r5, 3352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3312(%r3)
	ld %r4, 3320(%r3)
	ld %r5, 3360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3320(%r3)
	ld %r4, 3328(%r3)
	ld %r5, 3368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3328(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 3376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3336(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 3384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3344(%r3)
	ld %r4, 3352(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3352(%r3)
	ld %r4, 3360(%r3)
	ld %r5, 192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3360(%r3)
	ld %r4, 3368(%r3)
	ld %r5, 200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3368(%r3)
	ld %r4, 3376(%r3)
	ld %r5, 208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3376(%r3)
	ld %r4, 3384(%r3)
	ld %r5, 216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3384(%r3)
	li %r4, 864
	li %r5, 184
	li %r6, 3312
	bl {vg_brainpoolp320r1_sub_mod_p}
	addi %r6, %r31, -45
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
	ld %r4, 3312(%r3)
	ld %r5, 864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3312(%r3)
	ld %r4, 3320(%r3)
	ld %r5, 872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3320(%r3)
	ld %r4, 3328(%r3)
	ld %r5, 880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3328(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3336(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3344(%r3)
	ld %r4, 624(%r3)
	std %r4, 3152(%r3)
	ld %r4, 632(%r3)
	std %r4, 3160(%r3)
	ld %r4, 640(%r3)
	std %r4, 3168(%r3)
	ld %r4, 648(%r3)
	std %r4, 3176(%r3)
	ld %r4, 656(%r3)
	std %r4, 3184(%r3)
	ld %r4, 664(%r3)
	std %r4, 3192(%r3)
	ld %r4, 672(%r3)
	std %r4, 3200(%r3)
	ld %r4, 680(%r3)
	std %r4, 3208(%r3)
	ld %r4, 688(%r3)
	std %r4, 3216(%r3)
	ld %r4, 696(%r3)
	std %r4, 3224(%r3)
	ld %r4, 704(%r3)
	std %r4, 3232(%r3)
	ld %r4, 712(%r3)
	std %r4, 3240(%r3)
	ld %r4, 720(%r3)
	std %r4, 3248(%r3)
	ld %r4, 728(%r3)
	std %r4, 3256(%r3)
	ld %r4, 736(%r3)
	std %r4, 3264(%r3)
	bl {vg_brainpoolp320r1_point_add}
	ld %r4, 3032(%r3)
	std %r4, 624(%r3)
	ld %r4, 3040(%r3)
	std %r4, 632(%r3)
	ld %r4, 3048(%r3)
	std %r4, 640(%r3)
	ld %r4, 3056(%r3)
	std %r4, 648(%r3)
	ld %r4, 3064(%r3)
	std %r4, 656(%r3)
	ld %r4, 3072(%r3)
	std %r4, 664(%r3)
	ld %r4, 3080(%r3)
	std %r4, 672(%r3)
	ld %r4, 3088(%r3)
	std %r4, 680(%r3)
	ld %r4, 3096(%r3)
	std %r4, 688(%r3)
	ld %r4, 3104(%r3)
	std %r4, 696(%r3)
	ld %r4, 3112(%r3)
	std %r4, 704(%r3)
	ld %r4, 3120(%r3)
	std %r4, 712(%r3)
	ld %r4, 3128(%r3)
	std %r4, 720(%r3)
	ld %r4, 3136(%r3)
	std %r4, 728(%r3)
	ld %r4, 3144(%r3)
	std %r4, 736(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	bl {vg_brainpoolp320r1_inv_mod_p}
	li %r4, 1424
	li %r5, 624
	li %r6, 1224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1464
	li %r5, 1424
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1504
	li %r5, 1464
	li %r6, 184
	bl {vg_brainpoolp320r1_add_mod_n}
	li %r4, 1544
	li %r5, 1304
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1344(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1348(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1352(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1356(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1360(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1364(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1368(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1372(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1376(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1380(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1344(%r3)
	ld %r4, 1352(%r3)
	or %r5, %r5, %r4
	ld %r4, 1360(%r3)
	or %r5, %r5, %r4
	ld %r4, 1368(%r3)
	or %r5, %r5, %r4
	ld %r4, 1376(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1304(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1308(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1312(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1316(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1320(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1324(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1328(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1332(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1336(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1340(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1304(%r3)
	ld %r4, 1312(%r3)
	or %r5, %r5, %r4
	ld %r4, 1320(%r3)
	or %r5, %r5, %r4
	ld %r4, 1328(%r3)
	or %r5, %r5, %r4
	ld %r4, 1336(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r5, 1504(%r3)
	ld %r4, 1512(%r3)
	or %r5, %r5, %r4
	ld %r4, 1520(%r3)
	or %r5, %r5, %r4
	ld %r4, 1528(%r3)
	or %r5, %r5, %r4
	ld %r4, 1536(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	bl {vg_brainpoolp320r1_inv_mod_n}
	li %r4, 1584
	li %r5, 1504
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1624
	li %r5, 1344
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1664
	li %r5, 1384
	li %r6, 464
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1704
	li %r5, 1584
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1704
	li %r5, 1704
	li %r6, 1664
	bl {vg_brainpoolp320r1_add_mod_n}
	li %r4, 1744
	li %r5, 1224
	li %r6, 1704
	bl {vg_brainpoolp320r1_mul_mod_n}
	li %r4, 1784
	li %r5, 1744
	li %r6, 224
	bl {vg_brainpoolp320r1_mul_mod_n}
	ld %r5, 1784(%r3)
	ld %r4, 1792(%r3)
	or %r5, %r5, %r4
	ld %r4, 1800(%r3)
	or %r5, %r5, %r4
	ld %r4, 1808(%r3)
	or %r5, %r5, %r4
	ld %r4, 1816(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r10, 1824(%r3)
	ld %r4, 1504(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1512(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1520(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1528(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1536(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 1784(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 1792(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	ld %r4, 1800(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 1808(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 1816(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
