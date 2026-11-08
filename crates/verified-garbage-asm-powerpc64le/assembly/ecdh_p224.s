// The functions of `src/ecdh_p224.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p224:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 20
	ldbrx %r8, %r4, %r9
	std %r8, 1056(%r3)
	li %r9, 12
	ldbrx %r8, %r4, %r9
	std %r8, 1064(%r3)
	li %r9, 4
	ldbrx %r8, %r4, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1080(%r3)
	li %r9, 20
	ldbrx %r8, %r4, %r9
	std %r8, 1088(%r3)
	li %r9, 12
	ldbrx %r8, %r4, %r9
	std %r8, 1096(%r3)
	li %r9, 4
	ldbrx %r8, %r4, %r9
	std %r8, 1104(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1112(%r3)
	li %r9, 20
	ldbrx %r8, %r4, %r9
	std %r8, 1120(%r3)
	li %r9, 12
	ldbrx %r8, %r4, %r9
	std %r8, 1128(%r3)
	li %r9, 4
	ldbrx %r8, %r4, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1144(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 64(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 68(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 72(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 76(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 80(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 84(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 88(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 92(%r3)
	lis %r11, 23644
	ori %r11, %r11, 10813
	stw %r11, 96(%r3)
	lis %r11, 5085
	ori %r11, %r11, 10565
	stw %r11, 100(%r3)
	lis %r11, -8008
	ori %r11, %r11, 61502
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 5794
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 120(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 124(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 160(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 164(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 168(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 172(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 176(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 180(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 188(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 192(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 196(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 204(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 224(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 228(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 232(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 252(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 256(%r3)
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 264(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 268(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 272(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 276(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 284(%r3)
	lis %r11, 11073
	ori %r11, %r11, 3430
	stw %r11, 288(%r3)
	lis %r11, -18886
	ori %r11, %r11, 27107
	stw %r11, 292(%r3)
	lis %r11, 26320
	ori %r11, %r11, 14642
	stw %r11, 296(%r3)
	lis %r11, 12656
	ori %r11, %r11, 18652
	stw %r11, 300(%r3)
	lis %r11, 22775
	ori %r11, %r11, 33779
	stw %r11, 304(%r3)
	lis %r11, -18068
	ori %r11, %r11, 12234
	stw %r11, 308(%r3)
	lis %r11, 32576
	ori %r11, %r11, 36537
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 27914
	ori %r11, %r11, 19178
	stw %r11, 320(%r3)
	lis %r11, -17264
	ori %r11, %r11, 21030
	stw %r11, 324(%r3)
	lis %r11, 24600
	ori %r11, %r11, 49066
	stw %r11, 328(%r3)
	lis %r11, -31451
	ori %r11, %r11, 38710
	stw %r11, 332(%r3)
	lis %r11, -1685
	ori %r11, %r11, 60421
	stw %r11, 336(%r3)
	lis %r11, 28115
	ori %r11, %r11, 44955
	stw %r11, 340(%r3)
	lis %r11, -24037
	ori %r11, %r11, 24160
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, -4109
	ori %r11, %r11, 60904
	stw %r11, 352(%r3)
	lis %r11, 11996
	ori %r11, %r11, 41445
	stw %r11, 356(%r3)
	lis %r11, 1331
	ori %r11, %r11, 23147
	stw %r11, 360(%r3)
	lis %r11, -1843
	ori %r11, %r11, 26411
	stw %r11, 364(%r3)
	lis %r11, 991
	ori %r11, %r11, 59512
	stw %r11, 368(%r3)
	lis %r11, -20823
	ori %r11, %r11, 50606
	stw %r11, 372(%r3)
	lis %r11, 24903
	ori %r11, %r11, 34545
	stw %r11, 376(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 380(%r3)
	lis %r11, 24401
	ori %r11, %r11, 32021
	stw %r11, 384(%r3)
	lis %r11, 10644
	ori %r11, %r11, 31337
	stw %r11, 388(%r3)
	lis %r11, 12758
	ori %r11, %r11, 16203
	stw %r11, 392(%r3)
	lis %r11, -21560
	ori %r11, %r11, 65369
	stw %r11, 396(%r3)
	lis %r11, -9871
	ori %r11, %r11, 18518
	stw %r11, 400(%r3)
	lis %r11, 27345
	ori %r11, %r11, 24444
	stw %r11, 404(%r3)
	lis %r11, -19991
	ori %r11, %r11, 31073
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, -23645
	ori %r11, %r11, 54723
	stw %r11, 420(%r3)
	lis %r11, -5086
	ori %r11, %r11, 54970
	stw %r11, 424(%r3)
	lis %r11, 8007
	ori %r11, %r11, 4033
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 59741
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 452(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 456(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 460(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 464(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 468(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 472(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 476(%r3)
	lis %r11, 23644
	ori %r11, %r11, 10811
	stw %r11, 480(%r3)
	lis %r11, 5085
	ori %r11, %r11, 10565
	stw %r11, 484(%r3)
	lis %r11, -8008
	ori %r11, %r11, 61502
	stw %r11, 488(%r3)
	lis %r11, -1
	ori %r11, %r11, 5794
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 504(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 508(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 516(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 520(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 524(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 528(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 532(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 536(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 540(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 544(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 548(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 560(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 564(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 568(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 572(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 576(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 580(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 584(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 588(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 592(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 596(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 600(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 604(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1472(%r3)
	or %r12, %r5, %r5
	li %r31, 32
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1056(%r4)
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
	bne %cr0, 20b
	li %r31, 32
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 448(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4352(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4353(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4354(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4355(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4356(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4357(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4358(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4359(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r31, 32
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 480(%r4)
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
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1312(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1316(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1320(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1324(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1328(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1332(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1340(%r3)
	lis %r11, 25536
	ori %r11, %r11, 22989
	stw %r11, 1344(%r3)
	lis %r11, -6296
	ori %r11, %r11, 52726
	stw %r11, 1348(%r3)
	lis %r11, -13072
	ori %r11, %r11, 4880
	stw %r11, 1352(%r3)
	lis %r11, 4218
	ori %r11, %r11, 49907
	stw %r11, 1356(%r3)
	lis %r11, -14254
	ori %r11, %r11, 33105
	stw %r11, 1360(%r3)
	lis %r11, 15822
	ori %r11, %r11, 47768
	stw %r11, 1364(%r3)
	lis %r11, 32704
	ori %r11, %r11, 12179
	stw %r11, 1368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1372(%r3)
	addi %r6, %r12, 1
	li %r9, 20
	ldbrx %r8, %r6, %r9
	std %r8, 1120(%r3)
	li %r9, 12
	ldbrx %r8, %r6, %r9
	std %r8, 1128(%r3)
	li %r9, 4
	ldbrx %r8, %r6, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1144(%r3)
	addi %r6, %r6, 28
	li %r9, 20
	ldbrx %r8, %r6, %r9
	std %r8, 1216(%r3)
	li %r9, 12
	ldbrx %r8, %r6, %r9
	std %r8, 1224(%r3)
	li %r9, 4
	ldbrx %r8, %r6, %r9
	std %r8, 1232(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 32, 32
	std %r8, 1240(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1120(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1124(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1128(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1132(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1136(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1140(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1144(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1148(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1216(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1220(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1224(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1228(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1232(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1236(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1240(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1244(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	li %r4, 1152
	li %r5, 1120
	li %r6, 1312
	bl {vg_p224_mul_mod_p}
	li %r4, 1184
	li %r5, 1216
	li %r6, 1312
	bl {vg_p224_mul_mod_p}
	li %r4, 1248
	li %r5, 1184
	li %r6, 1184
	bl {vg_p224_mul_mod_p}
	li %r4, 1376
	li %r5, 1152
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1408
	li %r5, 1376
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1376
	li %r5, 256
	li %r6, 1152
	bl {vg_p224_mul_mod_p}
	li %r4, 1280
	li %r5, 1408
	li %r6, 1376
	bl {vg_p224_add_mod_p}
	li %r4, 1408
	li %r5, 1280
	li %r6, 1344
	bl {vg_p224_add_mod_p}
	li %r4, 1376
	li %r5, 1248
	li %r6, 1408
	bl {vg_p224_sub_mod_p}
	ld %r5, 1376(%r3)
	ld %r4, 1384(%r3)
	or %r5, %r5, %r4
	ld %r4, 1392(%r3)
	or %r5, %r5, %r4
	ld %r4, 1400(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	li %r4, 0
	subf %r5, %r5, %r4
	addi %r5, %r5, -1
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r10, 1472(%r3)
	ld %r4, 320(%r3)
	ld %r5, 1152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1280(%r3)
	ld %r4, 328(%r3)
	ld %r5, 1160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1288(%r3)
	ld %r4, 336(%r3)
	ld %r5, 1168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1296(%r3)
	ld %r4, 344(%r3)
	ld %r5, 1176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1304(%r3)
	ld %r4, 352(%r3)
	ld %r5, 1184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1440(%r3)
	ld %r4, 360(%r3)
	ld %r5, 1192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1448(%r3)
	ld %r4, 368(%r3)
	ld %r5, 1200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 376(%r3)
	ld %r5, 1208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	ld %r4, 160(%r3)
	std %r4, 4864(%r3)
	ld %r4, 168(%r3)
	std %r4, 4872(%r3)
	ld %r4, 176(%r3)
	std %r4, 4880(%r3)
	ld %r4, 184(%r3)
	std %r4, 4888(%r3)
	ld %r4, 224(%r3)
	std %r4, 4896(%r3)
	ld %r4, 232(%r3)
	std %r4, 4904(%r3)
	ld %r4, 240(%r3)
	std %r4, 4912(%r3)
	ld %r4, 248(%r3)
	std %r4, 4920(%r3)
	ld %r4, 160(%r3)
	std %r4, 4928(%r3)
	ld %r4, 168(%r3)
	std %r4, 4936(%r3)
	ld %r4, 176(%r3)
	std %r4, 4944(%r3)
	ld %r4, 184(%r3)
	std %r4, 4952(%r3)
	ld %r4, 1280(%r3)
	std %r4, 4960(%r3)
	ld %r4, 1288(%r3)
	std %r4, 4968(%r3)
	ld %r4, 1296(%r3)
	std %r4, 4976(%r3)
	ld %r4, 1304(%r3)
	std %r4, 4984(%r3)
	ld %r4, 1440(%r3)
	std %r4, 4992(%r3)
	ld %r4, 1448(%r3)
	std %r4, 5000(%r3)
	ld %r4, 1456(%r3)
	std %r4, 5008(%r3)
	ld %r4, 1464(%r3)
	std %r4, 5016(%r3)
	ld %r4, 224(%r3)
	std %r4, 5024(%r3)
	ld %r4, 232(%r3)
	std %r4, 5032(%r3)
	ld %r4, 240(%r3)
	std %r4, 5040(%r3)
	ld %r4, 248(%r3)
	std %r4, 5048(%r3)
	ld %r4, 1280(%r3)
	std %r4, 608(%r3)
	ld %r4, 1288(%r3)
	std %r4, 616(%r3)
	ld %r4, 1296(%r3)
	std %r4, 624(%r3)
	ld %r4, 1304(%r3)
	std %r4, 632(%r3)
	ld %r4, 1440(%r3)
	std %r4, 640(%r3)
	ld %r4, 1448(%r3)
	std %r4, 648(%r3)
	ld %r4, 1456(%r3)
	std %r4, 656(%r3)
	ld %r4, 1464(%r3)
	std %r4, 664(%r3)
	ld %r4, 224(%r3)
	std %r4, 672(%r3)
	ld %r4, 232(%r3)
	std %r4, 680(%r3)
	ld %r4, 240(%r3)
	std %r4, 688(%r3)
	ld %r4, 248(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5056(%r3)
	ld %r4, 712(%r3)
	std %r4, 5064(%r3)
	ld %r4, 720(%r3)
	std %r4, 5072(%r3)
	ld %r4, 728(%r3)
	std %r4, 5080(%r3)
	ld %r4, 736(%r3)
	std %r4, 5088(%r3)
	ld %r4, 744(%r3)
	std %r4, 5096(%r3)
	ld %r4, 752(%r3)
	std %r4, 5104(%r3)
	ld %r4, 760(%r3)
	std %r4, 5112(%r3)
	ld %r4, 768(%r3)
	std %r4, 5120(%r3)
	ld %r4, 776(%r3)
	std %r4, 5128(%r3)
	ld %r4, 784(%r3)
	std %r4, 5136(%r3)
	ld %r4, 792(%r3)
	std %r4, 5144(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5152(%r3)
	ld %r4, 712(%r3)
	std %r4, 5160(%r3)
	ld %r4, 720(%r3)
	std %r4, 5168(%r3)
	ld %r4, 728(%r3)
	std %r4, 5176(%r3)
	ld %r4, 736(%r3)
	std %r4, 5184(%r3)
	ld %r4, 744(%r3)
	std %r4, 5192(%r3)
	ld %r4, 752(%r3)
	std %r4, 5200(%r3)
	ld %r4, 760(%r3)
	std %r4, 5208(%r3)
	ld %r4, 768(%r3)
	std %r4, 5216(%r3)
	ld %r4, 776(%r3)
	std %r4, 5224(%r3)
	ld %r4, 784(%r3)
	std %r4, 5232(%r3)
	ld %r4, 792(%r3)
	std %r4, 5240(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5248(%r3)
	ld %r4, 712(%r3)
	std %r4, 5256(%r3)
	ld %r4, 720(%r3)
	std %r4, 5264(%r3)
	ld %r4, 728(%r3)
	std %r4, 5272(%r3)
	ld %r4, 736(%r3)
	std %r4, 5280(%r3)
	ld %r4, 744(%r3)
	std %r4, 5288(%r3)
	ld %r4, 752(%r3)
	std %r4, 5296(%r3)
	ld %r4, 760(%r3)
	std %r4, 5304(%r3)
	ld %r4, 768(%r3)
	std %r4, 5312(%r3)
	ld %r4, 776(%r3)
	std %r4, 5320(%r3)
	ld %r4, 784(%r3)
	std %r4, 5328(%r3)
	ld %r4, 792(%r3)
	std %r4, 5336(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5344(%r3)
	ld %r4, 712(%r3)
	std %r4, 5352(%r3)
	ld %r4, 720(%r3)
	std %r4, 5360(%r3)
	ld %r4, 728(%r3)
	std %r4, 5368(%r3)
	ld %r4, 736(%r3)
	std %r4, 5376(%r3)
	ld %r4, 744(%r3)
	std %r4, 5384(%r3)
	ld %r4, 752(%r3)
	std %r4, 5392(%r3)
	ld %r4, 760(%r3)
	std %r4, 5400(%r3)
	ld %r4, 768(%r3)
	std %r4, 5408(%r3)
	ld %r4, 776(%r3)
	std %r4, 5416(%r3)
	ld %r4, 784(%r3)
	std %r4, 5424(%r3)
	ld %r4, 792(%r3)
	std %r4, 5432(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5440(%r3)
	ld %r4, 712(%r3)
	std %r4, 5448(%r3)
	ld %r4, 720(%r3)
	std %r4, 5456(%r3)
	ld %r4, 728(%r3)
	std %r4, 5464(%r3)
	ld %r4, 736(%r3)
	std %r4, 5472(%r3)
	ld %r4, 744(%r3)
	std %r4, 5480(%r3)
	ld %r4, 752(%r3)
	std %r4, 5488(%r3)
	ld %r4, 760(%r3)
	std %r4, 5496(%r3)
	ld %r4, 768(%r3)
	std %r4, 5504(%r3)
	ld %r4, 776(%r3)
	std %r4, 5512(%r3)
	ld %r4, 784(%r3)
	std %r4, 5520(%r3)
	ld %r4, 792(%r3)
	std %r4, 5528(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5536(%r3)
	ld %r4, 712(%r3)
	std %r4, 5544(%r3)
	ld %r4, 720(%r3)
	std %r4, 5552(%r3)
	ld %r4, 728(%r3)
	std %r4, 5560(%r3)
	ld %r4, 736(%r3)
	std %r4, 5568(%r3)
	ld %r4, 744(%r3)
	std %r4, 5576(%r3)
	ld %r4, 752(%r3)
	std %r4, 5584(%r3)
	ld %r4, 760(%r3)
	std %r4, 5592(%r3)
	ld %r4, 768(%r3)
	std %r4, 5600(%r3)
	ld %r4, 776(%r3)
	std %r4, 5608(%r3)
	ld %r4, 784(%r3)
	std %r4, 5616(%r3)
	ld %r4, 792(%r3)
	std %r4, 5624(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5632(%r3)
	ld %r4, 712(%r3)
	std %r4, 5640(%r3)
	ld %r4, 720(%r3)
	std %r4, 5648(%r3)
	ld %r4, 728(%r3)
	std %r4, 5656(%r3)
	ld %r4, 736(%r3)
	std %r4, 5664(%r3)
	ld %r4, 744(%r3)
	std %r4, 5672(%r3)
	ld %r4, 752(%r3)
	std %r4, 5680(%r3)
	ld %r4, 760(%r3)
	std %r4, 5688(%r3)
	ld %r4, 768(%r3)
	std %r4, 5696(%r3)
	ld %r4, 776(%r3)
	std %r4, 5704(%r3)
	ld %r4, 784(%r3)
	std %r4, 5712(%r3)
	ld %r4, 792(%r3)
	std %r4, 5720(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5728(%r3)
	ld %r4, 712(%r3)
	std %r4, 5736(%r3)
	ld %r4, 720(%r3)
	std %r4, 5744(%r3)
	ld %r4, 728(%r3)
	std %r4, 5752(%r3)
	ld %r4, 736(%r3)
	std %r4, 5760(%r3)
	ld %r4, 744(%r3)
	std %r4, 5768(%r3)
	ld %r4, 752(%r3)
	std %r4, 5776(%r3)
	ld %r4, 760(%r3)
	std %r4, 5784(%r3)
	ld %r4, 768(%r3)
	std %r4, 5792(%r3)
	ld %r4, 776(%r3)
	std %r4, 5800(%r3)
	ld %r4, 784(%r3)
	std %r4, 5808(%r3)
	ld %r4, 792(%r3)
	std %r4, 5816(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5824(%r3)
	ld %r4, 712(%r3)
	std %r4, 5832(%r3)
	ld %r4, 720(%r3)
	std %r4, 5840(%r3)
	ld %r4, 728(%r3)
	std %r4, 5848(%r3)
	ld %r4, 736(%r3)
	std %r4, 5856(%r3)
	ld %r4, 744(%r3)
	std %r4, 5864(%r3)
	ld %r4, 752(%r3)
	std %r4, 5872(%r3)
	ld %r4, 760(%r3)
	std %r4, 5880(%r3)
	ld %r4, 768(%r3)
	std %r4, 5888(%r3)
	ld %r4, 776(%r3)
	std %r4, 5896(%r3)
	ld %r4, 784(%r3)
	std %r4, 5904(%r3)
	ld %r4, 792(%r3)
	std %r4, 5912(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 5920(%r3)
	ld %r4, 712(%r3)
	std %r4, 5928(%r3)
	ld %r4, 720(%r3)
	std %r4, 5936(%r3)
	ld %r4, 728(%r3)
	std %r4, 5944(%r3)
	ld %r4, 736(%r3)
	std %r4, 5952(%r3)
	ld %r4, 744(%r3)
	std %r4, 5960(%r3)
	ld %r4, 752(%r3)
	std %r4, 5968(%r3)
	ld %r4, 760(%r3)
	std %r4, 5976(%r3)
	ld %r4, 768(%r3)
	std %r4, 5984(%r3)
	ld %r4, 776(%r3)
	std %r4, 5992(%r3)
	ld %r4, 784(%r3)
	std %r4, 6000(%r3)
	ld %r4, 792(%r3)
	std %r4, 6008(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6016(%r3)
	ld %r4, 712(%r3)
	std %r4, 6024(%r3)
	ld %r4, 720(%r3)
	std %r4, 6032(%r3)
	ld %r4, 728(%r3)
	std %r4, 6040(%r3)
	ld %r4, 736(%r3)
	std %r4, 6048(%r3)
	ld %r4, 744(%r3)
	std %r4, 6056(%r3)
	ld %r4, 752(%r3)
	std %r4, 6064(%r3)
	ld %r4, 760(%r3)
	std %r4, 6072(%r3)
	ld %r4, 768(%r3)
	std %r4, 6080(%r3)
	ld %r4, 776(%r3)
	std %r4, 6088(%r3)
	ld %r4, 784(%r3)
	std %r4, 6096(%r3)
	ld %r4, 792(%r3)
	std %r4, 6104(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6112(%r3)
	ld %r4, 712(%r3)
	std %r4, 6120(%r3)
	ld %r4, 720(%r3)
	std %r4, 6128(%r3)
	ld %r4, 728(%r3)
	std %r4, 6136(%r3)
	ld %r4, 736(%r3)
	std %r4, 6144(%r3)
	ld %r4, 744(%r3)
	std %r4, 6152(%r3)
	ld %r4, 752(%r3)
	std %r4, 6160(%r3)
	ld %r4, 760(%r3)
	std %r4, 6168(%r3)
	ld %r4, 768(%r3)
	std %r4, 6176(%r3)
	ld %r4, 776(%r3)
	std %r4, 6184(%r3)
	ld %r4, 784(%r3)
	std %r4, 6192(%r3)
	ld %r4, 792(%r3)
	std %r4, 6200(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6208(%r3)
	ld %r4, 712(%r3)
	std %r4, 6216(%r3)
	ld %r4, 720(%r3)
	std %r4, 6224(%r3)
	ld %r4, 728(%r3)
	std %r4, 6232(%r3)
	ld %r4, 736(%r3)
	std %r4, 6240(%r3)
	ld %r4, 744(%r3)
	std %r4, 6248(%r3)
	ld %r4, 752(%r3)
	std %r4, 6256(%r3)
	ld %r4, 760(%r3)
	std %r4, 6264(%r3)
	ld %r4, 768(%r3)
	std %r4, 6272(%r3)
	ld %r4, 776(%r3)
	std %r4, 6280(%r3)
	ld %r4, 784(%r3)
	std %r4, 6288(%r3)
	ld %r4, 792(%r3)
	std %r4, 6296(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 608
	li %r6, 1280
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 1440
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 672
	li %r6, 224
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 1280
	li %r6, 1440
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 1440
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1280
	li %r6, 224
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 6304(%r3)
	ld %r4, 712(%r3)
	std %r4, 6312(%r3)
	ld %r4, 720(%r3)
	std %r4, 6320(%r3)
	ld %r4, 728(%r3)
	std %r4, 6328(%r3)
	ld %r4, 736(%r3)
	std %r4, 6336(%r3)
	ld %r4, 744(%r3)
	std %r4, 6344(%r3)
	ld %r4, 752(%r3)
	std %r4, 6352(%r3)
	ld %r4, 760(%r3)
	std %r4, 6360(%r3)
	ld %r4, 768(%r3)
	std %r4, 6368(%r3)
	ld %r4, 776(%r3)
	std %r4, 6376(%r3)
	ld %r4, 784(%r3)
	std %r4, 6384(%r3)
	ld %r4, 792(%r3)
	std %r4, 6392(%r3)
	ld %r4, 704(%r3)
	std %r4, 608(%r3)
	ld %r4, 712(%r3)
	std %r4, 616(%r3)
	ld %r4, 720(%r3)
	std %r4, 624(%r3)
	ld %r4, 728(%r3)
	std %r4, 632(%r3)
	ld %r4, 736(%r3)
	std %r4, 640(%r3)
	ld %r4, 744(%r3)
	std %r4, 648(%r3)
	ld %r4, 752(%r3)
	std %r4, 656(%r3)
	ld %r4, 760(%r3)
	std %r4, 664(%r3)
	ld %r4, 768(%r3)
	std %r4, 672(%r3)
	ld %r4, 776(%r3)
	std %r4, 680(%r3)
	ld %r4, 784(%r3)
	std %r4, 688(%r3)
	ld %r4, 792(%r3)
	std %r4, 696(%r3)
	ld %r4, 160(%r3)
	std %r4, 512(%r3)
	ld %r4, 168(%r3)
	std %r4, 520(%r3)
	ld %r4, 176(%r3)
	std %r4, 528(%r3)
	ld %r4, 184(%r3)
	std %r4, 536(%r3)
	ld %r4, 224(%r3)
	std %r4, 544(%r3)
	ld %r4, 232(%r3)
	std %r4, 552(%r3)
	ld %r4, 240(%r3)
	std %r4, 560(%r3)
	ld %r4, 248(%r3)
	std %r4, 568(%r3)
	ld %r4, 160(%r3)
	std %r4, 576(%r3)
	ld %r4, 168(%r3)
	std %r4, 584(%r3)
	ld %r4, 176(%r3)
	std %r4, 592(%r3)
	ld %r4, 184(%r3)
	std %r4, 600(%r3)
	li %r31, 64
23:
	addi %r31, %r31, -1
	li %r4, 608
	li %r5, 512
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 800
	li %r5, 576
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	li %r4, 640
	li %r5, 544
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 576
	li %r6, 160
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 608
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 864
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 896
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 704
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 704
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 736
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 864
	li %r6, 608
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 896
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 640
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 608
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 608
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 864
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 896
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 704
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 704
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 704
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 608
	li %r6, 896
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 736
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 896
	bl {vg_p224_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 864
	li %r6, 608
	bl {vg_p224_sub_mod_p}
	li %r4, 640
	li %r5, 896
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 512
	li %r5, 608
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 800
	li %r5, 672
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 576
	li %r5, 800
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 544
	li %r5, 640
	li %r6, 160
	bl {vg_p224_add_mod_p}
	ld %r5, 576(%r3)
	ld %r4, 584(%r3)
	or %r5, %r5, %r4
	ld %r4, 592(%r3)
	or %r5, %r5, %r4
	ld %r4, 600(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	or %r10, %r5, %r5
	ld %r4, 224(%r3)
	ld %r5, 544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 232(%r3)
	ld %r5, 552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 240(%r3)
	ld %r5, 560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 248(%r3)
	ld %r5, 568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	rldicr %r4, %r31, 2, 61
	add %r4, %r3, %r4
	lbz %r9, 4099(%r4)
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 4864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 4872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 4880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 4888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 4896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 4904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 4912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 4920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 4928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 4936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 4944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 4952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 1
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 4960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 4968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 4976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 4984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 4992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 2
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 3
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 4
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 5
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 6
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 7
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 8
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 9
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 10
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 5904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 5912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 11
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 5920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 5928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 5936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 5944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 5952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 5960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 5968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 5976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 5984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 5992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 12
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 13
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 14
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r5, 15
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 608(%r3)
	ld %r5, 6304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 608(%r3)
	ld %r4, 616(%r3)
	ld %r5, 6312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 616(%r3)
	ld %r4, 624(%r3)
	ld %r5, 6320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 624(%r3)
	ld %r4, 632(%r3)
	ld %r5, 6328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 632(%r3)
	ld %r4, 640(%r3)
	ld %r5, 6336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 640(%r3)
	ld %r4, 648(%r3)
	ld %r5, 6344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 648(%r3)
	ld %r4, 656(%r3)
	ld %r5, 6352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 656(%r3)
	ld %r4, 664(%r3)
	ld %r5, 6360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 664(%r3)
	ld %r4, 672(%r3)
	ld %r5, 6368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 672(%r3)
	ld %r4, 680(%r3)
	ld %r5, 6376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 680(%r3)
	ld %r4, 688(%r3)
	ld %r5, 6384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 688(%r3)
	ld %r4, 696(%r3)
	ld %r5, 6392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 696(%r3)
	li %r4, 800
	li %r5, 512
	li %r6, 608
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 544
	li %r6, 640
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 576
	li %r6, 672
	bl {vg_p224_mul_mod_p}
	li %r4, 896
	li %r5, 512
	li %r6, 544
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 608
	li %r6, 640
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p224_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p224_sub_mod_p}
	li %r4, 928
	li %r5, 544
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 640
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 512
	li %r6, 576
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 608
	li %r6, 672
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 800
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 736
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 1344
	li %r6, 864
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 736
	li %r6, 768
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 704
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 768
	bl {vg_p224_add_mod_p}
	li %r4, 768
	li %r5, 832
	li %r6, 704
	bl {vg_p224_sub_mod_p}
	li %r4, 704
	li %r5, 832
	li %r6, 704
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 1344
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 864
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 864
	li %r5, 832
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 800
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 736
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 736
	li %r5, 832
	li %r6, 736
	bl {vg_p224_add_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 800
	bl {vg_p224_add_mod_p}
	li %r4, 800
	li %r5, 800
	li %r6, 864
	bl {vg_p224_sub_mod_p}
	li %r4, 832
	li %r5, 928
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 736
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 864
	bl {vg_p224_add_mod_p}
	li %r4, 704
	li %r5, 896
	li %r6, 704
	bl {vg_p224_mul_mod_p}
	li %r4, 704
	li %r5, 704
	li %r6, 832
	bl {vg_p224_sub_mod_p}
	li %r4, 768
	li %r5, 928
	li %r6, 768
	bl {vg_p224_mul_mod_p}
	li %r4, 832
	li %r5, 896
	li %r6, 800
	bl {vg_p224_mul_mod_p}
	li %r4, 768
	li %r5, 768
	li %r6, 832
	bl {vg_p224_add_mod_p}
	ld %r4, 704(%r3)
	std %r4, 512(%r3)
	ld %r4, 712(%r3)
	std %r4, 520(%r3)
	ld %r4, 720(%r3)
	std %r4, 528(%r3)
	ld %r4, 728(%r3)
	std %r4, 536(%r3)
	ld %r4, 736(%r3)
	std %r4, 544(%r3)
	ld %r4, 744(%r3)
	std %r4, 552(%r3)
	ld %r4, 752(%r3)
	std %r4, 560(%r3)
	ld %r4, 760(%r3)
	std %r4, 568(%r3)
	ld %r4, 768(%r3)
	std %r4, 576(%r3)
	ld %r4, 776(%r3)
	std %r4, 584(%r3)
	ld %r4, 784(%r3)
	std %r4, 592(%r3)
	ld %r4, 792(%r3)
	std %r4, 600(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 224(%r3)
	std %r4, 992(%r3)
	ld %r4, 232(%r3)
	std %r4, 1000(%r3)
	ld %r4, 240(%r3)
	std %r4, 1008(%r3)
	ld %r4, 248(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 576
	bl {vg_p224_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4352(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 992(%r3)
	ld %r5, 1024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 1032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 1040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 1048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1152
	li %r5, 512
	li %r6, 992
	bl {vg_p224_mul_mod_p}
	li %r4, 1184
	li %r5, 1152
	li %r6, 192
	bl {vg_p224_mul_mod_p}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1088(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1092(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1096(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1100(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1104(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1108(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1112(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1116(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1088(%r3)
	ld %r4, 1096(%r3)
	or %r5, %r5, %r4
	ld %r4, 1104(%r3)
	or %r5, %r5, %r4
	ld %r4, 1112(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r5, 576(%r3)
	ld %r4, 584(%r3)
	or %r5, %r5, %r4
	ld %r4, 592(%r3)
	or %r5, %r5, %r4
	ld %r4, 600(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r10, 1472(%r3)
	ld %r4, 1184(%r3)
	and %r4, %r4, %r10
	li %r6, 20
	stdbrx %r4, %r14, %r6
	ld %r4, 1192(%r3)
	and %r4, %r4, %r10
	li %r6, 12
	stdbrx %r4, %r14, %r6
	ld %r4, 1200(%r3)
	and %r4, %r4, %r10
	li %r6, 4
	stdbrx %r4, %r14, %r6
	ld %r4, 1208(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 40, 24
	stb %r5, 0(%r14)
	rldicl %r5, %r4, 48, 16
	stb %r5, 1(%r14)
	rldicl %r5, %r4, 56, 8
	stb %r5, 2(%r14)
	stb %r4, 3(%r14)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
