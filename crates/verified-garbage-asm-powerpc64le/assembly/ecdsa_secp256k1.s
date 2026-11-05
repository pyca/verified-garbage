// The functions of `src/ecdsa_secp256k1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_verify:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1056(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1064(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1080(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1088(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1096(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1104(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1112(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1120(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1128(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1144(%r3)
	lis %r11, -1
	ori %r11, %r11, 64559
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 92(%r3)
	lis %r11, -12234
	ori %r11, %r11, 16705
	stw %r11, 96(%r3)
	lis %r11, -16430
	ori %r11, %r11, 24204
	stw %r11, 100(%r3)
	lis %r11, -20664
	ori %r11, %r11, 41019
	stw %r11, 104(%r3)
	lis %r11, -17746
	ori %r11, %r11, 56550
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 120(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	ori %r11, %r11, 977
	stw %r11, 224(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 0
	stw %r11, 256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 284(%r3)
	lis %r11, 0
	ori %r11, %r11, 20517
	stw %r11, 288(%r3)
	lis %r11, 0
	ori %r11, %r11, 21
	stw %r11, 292(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 296(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 300(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 304(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 308(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 18558
	ori %r11, %r11, 8343
	stw %r11, 320(%r3)
	lis %r11, -10442
	ori %r11, %r11, 11866
	stw %r11, 324(%r3)
	lis %r11, 10684
	ori %r11, %r11, 26331
	stw %r11, 328(%r3)
	lis %r11, 8990
	ori %r11, %r11, 10579
	stw %r11, 332(%r3)
	lis %r11, 13309
	ori %r11, %r11, 4764
	stw %r11, 336(%r3)
	lis %r11, -26721
	ori %r11, %r11, 18624
	stw %r11, 340(%r3)
	lis %r11, -5880
	ori %r11, %r11, 40776
	stw %r11, 344(%r3)
	lis %r11, -26239
	ori %r11, %r11, 58947
	stw %r11, 348(%r3)
	lis %r11, -11301
	ori %r11, %r11, 44002
	stw %r11, 352(%r3)
	lis %r11, -20130
	ori %r11, %r11, 42706
	stw %r11, 356(%r3)
	lis %r11, 7965
	ori %r11, %r11, 50765
	stw %r11, 360(%r3)
	lis %r11, -29188
	ori %r11, %r11, 23901
	stw %r11, 364(%r3)
	lis %r11, -21479
	ori %r11, %r11, 49462
	stw %r11, 368(%r3)
	lis %r11, 28854
	ori %r11, %r11, 46490
	stw %r11, 372(%r3)
	lis %r11, -11099
	ori %r11, %r11, 33494
	stw %r11, 376(%r3)
	lis %r11, -12481
	ori %r11, %r11, 34079
	stw %r11, 380(%r3)
	lis %r11, 26583
	ori %r11, %r11, 53568
	stw %r11, 384(%r3)
	lis %r11, -30356
	ori %r11, %r11, 61972
	stw %r11, 388(%r3)
	lis %r11, 3708
	ori %r11, %r11, 63608
	stw %r11, 392(%r3)
	lis %r11, 29716
	ori %r11, %r11, 38594
	stw %r11, 396(%r3)
	lis %r11, 23501
	ori %r11, %r11, 1990
	stw %r11, 400(%r3)
	lis %r11, -6505
	ori %r11, %r11, 62948
	stw %r11, 404(%r3)
	lis %r11, -32314
	ori %r11, %r11, 39877
	stw %r11, 408(%r3)
	lis %r11, -25241
	ori %r11, %r11, 7381
	stw %r11, 412(%r3)
	lis %r11, 12233
	ori %r11, %r11, 48831
	stw %r11, 416(%r3)
	lis %r11, 16429
	ori %r11, %r11, 41331
	stw %r11, 420(%r3)
	lis %r11, 20663
	ori %r11, %r11, 24516
	stw %r11, 424(%r3)
	lis %r11, 17745
	ori %r11, %r11, 8985
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
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
	ori %r11, %r11, 64557
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 452(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 456(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 476(%r3)
	lis %r11, -12234
	ori %r11, %r11, 16703
	stw %r11, 480(%r3)
	lis %r11, -16430
	ori %r11, %r11, 24204
	stw %r11, 484(%r3)
	lis %r11, -20664
	ori %r11, %r11, 41019
	stw %r11, 488(%r3)
	lis %r11, -17746
	ori %r11, %r11, 56550
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	ori %r11, %r11, 977
	stw %r11, 544(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 548(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 552(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	addi %r6, %r12, 32
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1024(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1032(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1040(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1048(%r3)
	lis %r11, 14
	ori %r11, %r11, 37025
	stw %r11, 1312(%r3)
	lis %r11, 0
	ori %r11, %r11, 1954
	stw %r11, 1316(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1320(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1324(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1328(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1332(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1340(%r3)
	lis %r11, 0
	ori %r11, %r11, 6839
	stw %r11, 1344(%r3)
	lis %r11, 0
	ori %r11, %r11, 7
	stw %r11, 1348(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1352(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1356(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1360(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1364(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1372(%r3)
	addi %r6, %r14, 1
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1120(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1128(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1144(%r3)
	addi %r6, %r6, 32
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1216(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1224(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1232(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1240(%r3)
	lbz %r4, 0(%r14)
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
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1184
	li %r5, 1216
	li %r6, 1312
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1248
	li %r5, 1184
	li %r6, 1184
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1376
	li %r5, 1152
	li %r6, 1152
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1408
	li %r5, 1376
	li %r6, 1152
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1376
	li %r5, 256
	li %r6, 1152
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1280
	li %r5, 1408
	li %r6, 1376
	bl {vg_secp256k1_add_mod_p}
	li %r4, 1408
	li %r5, 1280
	li %r6, 1344
	bl {vg_secp256k1_add_mod_p}
	li %r4, 1376
	li %r5, 1248
	li %r6, 1408
	bl {vg_secp256k1_sub_mod_p}
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
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1056(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1060(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1064(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1068(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1072(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1076(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1080(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1084(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1056(%r3)
	ld %r4, 1064(%r3)
	or %r5, %r5, %r4
	ld %r4, 1072(%r3)
	or %r5, %r5, %r4
	ld %r4, 1080(%r3)
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
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1024(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1028(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1032(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1036(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1040(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1044(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1048(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1052(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1024(%r3)
	ld %r4, 1032(%r3)
	or %r5, %r5, %r4
	ld %r4, 1040(%r3)
	or %r5, %r5, %r4
	ld %r4, 1048(%r3)
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
	li %r4, 1248
	li %r5, 1024
	li %r6, 384
	bl {vg_secp256k1_mul_mod_n}
	ld %r4, 416(%r3)
	std %r4, 992(%r3)
	ld %r4, 424(%r3)
	std %r4, 1000(%r3)
	ld %r4, 432(%r3)
	std %r4, 1008(%r3)
	ld %r4, 440(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
23:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1024
	li %r5, 992
	li %r6, 1248
	bl {vg_secp256k1_mul_mod_n}
	add %r4, %r3, %r31
	lbz %r4, 4608(%r4)
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
	bne %cr0, 23b
	li %r4, 1344
	li %r5, 1088
	li %r6, 384
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1312
	li %r5, 1056
	li %r6, 384
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1376
	li %r5, 1344
	li %r6, 992
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1408
	li %r5, 1312
	li %r6, 992
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1152
	li %r5, 1376
	li %r6, 192
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1184
	li %r5, 1408
	li %r6, 192
	bl {vg_secp256k1_mul_mod_n}
	li %r31, 32
24:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1152(%r4)
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
	bne %cr0, 24b
	ld %r4, 320(%r3)
	std %r4, 3424(%r3)
	ld %r4, 328(%r3)
	std %r4, 3432(%r3)
	ld %r4, 336(%r3)
	std %r4, 3440(%r3)
	ld %r4, 344(%r3)
	std %r4, 3448(%r3)
	ld %r4, 352(%r3)
	std %r4, 3456(%r3)
	ld %r4, 360(%r3)
	std %r4, 3464(%r3)
	ld %r4, 368(%r3)
	std %r4, 3472(%r3)
	ld %r4, 376(%r3)
	std %r4, 3480(%r3)
	ld %r4, 224(%r3)
	std %r4, 3488(%r3)
	ld %r4, 232(%r3)
	std %r4, 3496(%r3)
	ld %r4, 240(%r3)
	std %r4, 3504(%r3)
	ld %r4, 248(%r3)
	std %r4, 3512(%r3)
	ld %r4, 256(%r3)
	std %r4, 3520(%r3)
	ld %r4, 264(%r3)
	std %r4, 3528(%r3)
	ld %r4, 272(%r3)
	std %r4, 3536(%r3)
	ld %r4, 280(%r3)
	std %r4, 3544(%r3)
	ld %r4, 288(%r3)
	std %r4, 3552(%r3)
	ld %r4, 296(%r3)
	std %r4, 3560(%r3)
	ld %r4, 304(%r3)
	std %r4, 3568(%r3)
	ld %r4, 312(%r3)
	std %r4, 3576(%r3)
	li %r31, 256
25:
	addi %r31, %r31, -1
	ld %r4, 512(%r3)
	std %r4, 3328(%r3)
	ld %r4, 520(%r3)
	std %r4, 3336(%r3)
	ld %r4, 528(%r3)
	std %r4, 3344(%r3)
	ld %r4, 536(%r3)
	std %r4, 3352(%r3)
	ld %r4, 544(%r3)
	std %r4, 3360(%r3)
	ld %r4, 552(%r3)
	std %r4, 3368(%r3)
	ld %r4, 560(%r3)
	std %r4, 3376(%r3)
	ld %r4, 568(%r3)
	std %r4, 3384(%r3)
	ld %r4, 576(%r3)
	std %r4, 3392(%r3)
	ld %r4, 584(%r3)
	std %r4, 3400(%r3)
	ld %r4, 592(%r3)
	std %r4, 3408(%r3)
	ld %r4, 600(%r3)
	std %r4, 3416(%r3)
	bl {vg_secp256k1_point_a0_double}
	ld %r4, 3232(%r3)
	std %r4, 3328(%r3)
	ld %r4, 3240(%r3)
	std %r4, 3336(%r3)
	ld %r4, 3248(%r3)
	std %r4, 3344(%r3)
	ld %r4, 3256(%r3)
	std %r4, 3352(%r3)
	ld %r4, 3264(%r3)
	std %r4, 3360(%r3)
	ld %r4, 3272(%r3)
	std %r4, 3368(%r3)
	ld %r4, 3280(%r3)
	std %r4, 3376(%r3)
	ld %r4, 3288(%r3)
	std %r4, 3384(%r3)
	ld %r4, 3296(%r3)
	std %r4, 3392(%r3)
	ld %r4, 3304(%r3)
	std %r4, 3400(%r3)
	ld %r4, 3312(%r3)
	std %r4, 3408(%r3)
	ld %r4, 3320(%r3)
	std %r4, 3416(%r3)
	bl {vg_secp256k1_point_a0_add_affine}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 3328(%r3)
	ld %r5, 3232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 512(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 3240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 520(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 3248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 528(%r3)
	ld %r4, 3352(%r3)
	ld %r5, 3256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 536(%r3)
	ld %r4, 3360(%r3)
	ld %r5, 3264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 3368(%r3)
	ld %r5, 3272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 3376(%r3)
	ld %r5, 3280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 3384(%r3)
	ld %r5, 3288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	ld %r4, 3392(%r3)
	ld %r5, 3296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 576(%r3)
	ld %r4, 3400(%r3)
	ld %r5, 3304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 584(%r3)
	ld %r4, 3408(%r3)
	ld %r5, 3312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 592(%r3)
	ld %r4, 3416(%r3)
	ld %r5, 3320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 600(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	ld %r4, 512(%r3)
	std %r4, 1376(%r3)
	ld %r4, 520(%r3)
	std %r4, 1384(%r3)
	ld %r4, 528(%r3)
	std %r4, 1392(%r3)
	ld %r4, 536(%r3)
	std %r4, 1400(%r3)
	ld %r4, 544(%r3)
	std %r4, 1408(%r3)
	ld %r4, 552(%r3)
	std %r4, 1416(%r3)
	ld %r4, 560(%r3)
	std %r4, 1424(%r3)
	ld %r4, 568(%r3)
	std %r4, 1432(%r3)
	ld %r4, 576(%r3)
	std %r4, 1248(%r3)
	ld %r4, 584(%r3)
	std %r4, 1256(%r3)
	ld %r4, 592(%r3)
	std %r4, 1264(%r3)
	ld %r4, 600(%r3)
	std %r4, 1272(%r3)
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
	ori %r11, %r11, 977
	stw %r11, 544(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 548(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 552(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	li %r31, 32
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1184(%r4)
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
	bne %cr0, 26b
	ld %r4, 1280(%r3)
	std %r4, 3424(%r3)
	ld %r4, 1288(%r3)
	std %r4, 3432(%r3)
	ld %r4, 1296(%r3)
	std %r4, 3440(%r3)
	ld %r4, 1304(%r3)
	std %r4, 3448(%r3)
	ld %r4, 1440(%r3)
	std %r4, 3456(%r3)
	ld %r4, 1448(%r3)
	std %r4, 3464(%r3)
	ld %r4, 1456(%r3)
	std %r4, 3472(%r3)
	ld %r4, 1464(%r3)
	std %r4, 3480(%r3)
	ld %r4, 224(%r3)
	std %r4, 3488(%r3)
	ld %r4, 232(%r3)
	std %r4, 3496(%r3)
	ld %r4, 240(%r3)
	std %r4, 3504(%r3)
	ld %r4, 248(%r3)
	std %r4, 3512(%r3)
	ld %r4, 256(%r3)
	std %r4, 3520(%r3)
	ld %r4, 264(%r3)
	std %r4, 3528(%r3)
	ld %r4, 272(%r3)
	std %r4, 3536(%r3)
	ld %r4, 280(%r3)
	std %r4, 3544(%r3)
	ld %r4, 288(%r3)
	std %r4, 3552(%r3)
	ld %r4, 296(%r3)
	std %r4, 3560(%r3)
	ld %r4, 304(%r3)
	std %r4, 3568(%r3)
	ld %r4, 312(%r3)
	std %r4, 3576(%r3)
	li %r31, 256
27:
	addi %r31, %r31, -1
	ld %r4, 512(%r3)
	std %r4, 3328(%r3)
	ld %r4, 520(%r3)
	std %r4, 3336(%r3)
	ld %r4, 528(%r3)
	std %r4, 3344(%r3)
	ld %r4, 536(%r3)
	std %r4, 3352(%r3)
	ld %r4, 544(%r3)
	std %r4, 3360(%r3)
	ld %r4, 552(%r3)
	std %r4, 3368(%r3)
	ld %r4, 560(%r3)
	std %r4, 3376(%r3)
	ld %r4, 568(%r3)
	std %r4, 3384(%r3)
	ld %r4, 576(%r3)
	std %r4, 3392(%r3)
	ld %r4, 584(%r3)
	std %r4, 3400(%r3)
	ld %r4, 592(%r3)
	std %r4, 3408(%r3)
	ld %r4, 600(%r3)
	std %r4, 3416(%r3)
	bl {vg_secp256k1_point_a0_double}
	ld %r4, 3232(%r3)
	std %r4, 3328(%r3)
	ld %r4, 3240(%r3)
	std %r4, 3336(%r3)
	ld %r4, 3248(%r3)
	std %r4, 3344(%r3)
	ld %r4, 3256(%r3)
	std %r4, 3352(%r3)
	ld %r4, 3264(%r3)
	std %r4, 3360(%r3)
	ld %r4, 3272(%r3)
	std %r4, 3368(%r3)
	ld %r4, 3280(%r3)
	std %r4, 3376(%r3)
	ld %r4, 3288(%r3)
	std %r4, 3384(%r3)
	ld %r4, 3296(%r3)
	std %r4, 3392(%r3)
	ld %r4, 3304(%r3)
	std %r4, 3400(%r3)
	ld %r4, 3312(%r3)
	std %r4, 3408(%r3)
	ld %r4, 3320(%r3)
	std %r4, 3416(%r3)
	bl {vg_secp256k1_point_a0_add_affine}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 3328(%r3)
	ld %r5, 3232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 512(%r3)
	ld %r4, 3336(%r3)
	ld %r5, 3240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 520(%r3)
	ld %r4, 3344(%r3)
	ld %r5, 3248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 528(%r3)
	ld %r4, 3352(%r3)
	ld %r5, 3256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 536(%r3)
	ld %r4, 3360(%r3)
	ld %r5, 3264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 3368(%r3)
	ld %r5, 3272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 3376(%r3)
	ld %r5, 3280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 3384(%r3)
	ld %r5, 3288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	ld %r4, 3392(%r3)
	ld %r5, 3296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 576(%r3)
	ld %r4, 3400(%r3)
	ld %r5, 3304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 584(%r3)
	ld %r4, 3408(%r3)
	ld %r5, 3312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 592(%r3)
	ld %r4, 3416(%r3)
	ld %r5, 3320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 600(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 800
	li %r5, 1376
	li %r6, 512
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 832
	li %r5, 1408
	li %r6, 544
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 864
	li %r5, 1248
	li %r6, 576
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 896
	li %r5, 1376
	li %r6, 1408
	bl {vg_secp256k1_add_mod_p}
	li %r4, 928
	li %r5, 512
	li %r6, 544
	bl {vg_secp256k1_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_secp256k1_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 928
	li %r5, 1376
	li %r6, 1248
	bl {vg_secp256k1_add_mod_p}
	li %r4, 960
	li %r5, 512
	li %r6, 576
	bl {vg_secp256k1_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 960
	li %r5, 800
	li %r6, 864
	bl {vg_secp256k1_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 960
	li %r5, 1408
	li %r6, 1248
	bl {vg_secp256k1_add_mod_p}
	li %r4, 608
	li %r5, 544
	li %r6, 576
	bl {vg_secp256k1_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 864
	bl {vg_secp256k1_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 672
	li %r5, 256
	li %r6, 928
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 608
	li %r5, 288
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 672
	li %r5, 608
	li %r6, 672
	bl {vg_secp256k1_add_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 672
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 672
	li %r5, 832
	li %r6, 672
	bl {vg_secp256k1_add_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 672
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_secp256k1_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 800
	bl {vg_secp256k1_add_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 928
	li %r5, 288
	li %r6, 928
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 864
	bl {vg_secp256k1_add_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 864
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 864
	bl {vg_secp256k1_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 928
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 800
	bl {vg_secp256k1_add_mod_p}
	li %r4, 800
	li %r5, 960
	li %r6, 928
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 608
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 800
	bl {vg_secp256k1_sub_mod_p}
	li %r4, 800
	li %r5, 896
	li %r6, 832
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 672
	li %r5, 960
	li %r6, 672
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_secp256k1_add_mod_p}
	ld %r4, 608(%r3)
	std %r4, 512(%r3)
	ld %r4, 616(%r3)
	std %r4, 520(%r3)
	ld %r4, 624(%r3)
	std %r4, 528(%r3)
	ld %r4, 632(%r3)
	std %r4, 536(%r3)
	ld %r4, 640(%r3)
	std %r4, 544(%r3)
	ld %r4, 648(%r3)
	std %r4, 552(%r3)
	ld %r4, 656(%r3)
	std %r4, 560(%r3)
	ld %r4, 664(%r3)
	std %r4, 568(%r3)
	ld %r4, 672(%r3)
	std %r4, 576(%r3)
	ld %r4, 680(%r3)
	std %r4, 584(%r3)
	ld %r4, 688(%r3)
	std %r4, 592(%r3)
	ld %r4, 696(%r3)
	std %r4, 600(%r3)
	ld %r4, 224(%r3)
	std %r4, 992(%r3)
	ld %r4, 232(%r3)
	std %r4, 1000(%r3)
	ld %r4, 240(%r3)
	std %r4, 1008(%r3)
	ld %r4, 248(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
28:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 576
	bl {vg_secp256k1_mul_mod_p}
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
	bne %cr0, 28b
	li %r4, 1152
	li %r5, 512
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1184
	li %r5, 1152
	li %r6, 192
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1280
	li %r5, 1184
	li %r6, 384
	bl {vg_secp256k1_mul_mod_n}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1312
	bl {vg_secp256k1_sub_mod_n}
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
	ld %r5, 1344(%r3)
	ld %r4, 1352(%r3)
	or %r5, %r5, %r4
	ld %r4, 1360(%r3)
	or %r5, %r5, %r4
	ld %r4, 1368(%r3)
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
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ecdsa_secp256k1_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -592(%r1)
	addi %r11, %r1, 0
	std %r3, 200(%r11)
	std %r4, 192(%r11)
	std %r5, 184(%r11)
	std %r7, 176(%r11)
	std %r8, 224(%r11)
	ld %r9, 32(%r8)
	std %r9, 208(%r11)
	ld %r9, 40(%r8)
	std %r9, 216(%r11)
	addi %r11, %r1, 0
	li %r9, 0
	std %r9, 304(%r11)
	std %r9, 312(%r11)
	std %r9, 320(%r11)
	std %r9, 328(%r11)
	std %r9, 336(%r11)
	std %r9, 344(%r11)
	std %r9, 352(%r11)
	std %r9, 360(%r11)
	std %r9, 368(%r11)
	ld %r6, 208(%r11)
	li %r9, 32
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 336
	subf %r5, %r6, %r5
	ld %r4, 184(%r11)
20:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	addi %r11, %r1, 0
	addi %r9, %r1, 304
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -12234
	ori %r12, %r12, 16705
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, -16430
	ori %r12, %r12, 24204
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -20664
	ori %r12, %r12, 41019
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -17746
	ori %r12, %r12, 56550
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65534
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 260
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 256
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 252
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 248
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 244
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 240
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 236
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 232
	stwbrx %r7, %r11, %r12
	addi %r11, %r1, 0
	lis %r9, 257
	ori %r9, %r9, 257
	li %r10, 0
	stw %r9, 96(%r11)
	stw %r10, 32(%r11)
	stw %r9, 100(%r11)
	stw %r10, 36(%r11)
	stw %r9, 104(%r11)
	stw %r10, 40(%r11)
	stw %r9, 108(%r11)
	stw %r10, 44(%r11)
	stw %r9, 112(%r11)
	stw %r10, 48(%r11)
	stw %r9, 116(%r11)
	stw %r10, 52(%r11)
	stw %r9, 120(%r11)
	stw %r10, 56(%r11)
	stw %r9, 124(%r11)
	stw %r10, 60(%r11)
	stw %r9, 128(%r11)
	stw %r10, 64(%r11)
	stw %r9, 132(%r11)
	stw %r10, 68(%r11)
	stw %r9, 136(%r11)
	stw %r10, 72(%r11)
	stw %r9, 140(%r11)
	stw %r10, 76(%r11)
	stw %r9, 144(%r11)
	stw %r10, 80(%r11)
	stw %r9, 148(%r11)
	stw %r10, 84(%r11)
	stw %r9, 152(%r11)
	stw %r10, 88(%r11)
	stw %r9, 156(%r11)
	stw %r10, 92(%r11)
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2257(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2261(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2265(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2269(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2289(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2293(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2317(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 65
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 1
	stb %r8, 2256(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2257(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2261(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2265(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2269(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2289(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2293(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2317(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 3072(%r12)
	std %r9, 0(%r12)
	ld %r9, 3080(%r12)
	std %r9, 8(%r12)
	ld %r9, 3088(%r12)
	std %r9, 16(%r12)
	ld %r9, 3096(%r12)
	std %r9, 24(%r12)
	ld %r9, 3104(%r12)
	std %r9, 32(%r12)
	ld %r9, 3112(%r12)
	std %r9, 40(%r12)
	ld %r9, 3120(%r12)
	std %r9, 48(%r12)
	ld %r9, 3128(%r12)
	std %r9, 56(%r12)
	ld %r9, 3136(%r12)
	std %r9, 64(%r12)
	ld %r9, 3144(%r12)
	std %r9, 72(%r12)
	ld %r9, 3152(%r12)
	std %r9, 80(%r12)
	ld %r9, 3160(%r12)
	std %r9, 88(%r12)
	ld %r9, 3168(%r12)
	std %r9, 96(%r12)
	ld %r9, 3176(%r12)
	std %r9, 104(%r12)
	ld %r9, 3184(%r12)
	std %r9, 112(%r12)
	ld %r9, 3192(%r12)
	std %r9, 120(%r12)
	ld %r9, 3200(%r12)
	std %r9, 128(%r12)
	ld %r9, 3208(%r12)
	std %r9, 136(%r12)
	ld %r9, 3216(%r12)
	std %r9, 144(%r12)
	ld %r9, 3224(%r12)
	std %r9, 152(%r12)
	ld %r9, 3232(%r12)
	std %r9, 160(%r12)
	ld %r9, 3240(%r12)
	std %r9, 168(%r12)
	ld %r9, 3248(%r12)
	std %r9, 176(%r12)
	ld %r9, 3256(%r12)
	std %r9, 184(%r12)
	ld %r9, 3264(%r12)
	std %r9, 192(%r12)
	ld %r9, 3272(%r12)
	std %r9, 200(%r12)
	ld %r9, 3280(%r12)
	std %r9, 208(%r12)
	ld %r9, 3288(%r12)
	std %r9, 216(%r12)
	ld %r9, 3296(%r12)
	std %r9, 224(%r12)
	ld %r9, 3304(%r12)
	std %r9, 232(%r12)
	ld %r9, 3312(%r12)
	std %r9, 240(%r12)
	ld %r9, 3320(%r12)
	std %r9, 248(%r12)
	ld %r9, 3328(%r12)
	std %r9, 256(%r12)
	ld %r9, 3336(%r12)
	std %r9, 264(%r12)
	ld %r9, 3344(%r12)
	std %r9, 272(%r12)
	ld %r9, 3352(%r12)
	std %r9, 280(%r12)
	ld %r9, 3360(%r12)
	std %r9, 288(%r12)
	ld %r9, 3368(%r12)
	std %r9, 296(%r12)
	ld %r9, 3376(%r12)
	std %r9, 304(%r12)
	ld %r9, 3384(%r12)
	std %r9, 312(%r12)
	ld %r9, 3392(%r12)
	std %r9, 320(%r12)
	ld %r9, 3400(%r12)
	std %r9, 328(%r12)
	ld %r9, 3408(%r12)
	std %r9, 336(%r12)
	ld %r9, 3416(%r12)
	std %r9, 344(%r12)
	ld %r9, 3424(%r12)
	std %r9, 352(%r12)
	ld %r9, 3432(%r12)
	std %r9, 360(%r12)
	ld %r9, 3440(%r12)
	std %r9, 368(%r12)
	ld %r9, 3448(%r12)
	std %r9, 376(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 65
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 168(%r11)
21:
	li %r9, 0
	addi %r11, %r1, 0
	std %r9, 160(%r11)
22:
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 3072(%r12)
	std %r9, 0(%r12)
	ld %r9, 3080(%r12)
	std %r9, 8(%r12)
	ld %r9, 3088(%r12)
	std %r9, 16(%r12)
	ld %r9, 3096(%r12)
	std %r9, 24(%r12)
	ld %r9, 3104(%r12)
	std %r9, 32(%r12)
	ld %r9, 3112(%r12)
	std %r9, 40(%r12)
	ld %r9, 3120(%r12)
	std %r9, 48(%r12)
	ld %r9, 3128(%r12)
	std %r9, 56(%r12)
	ld %r9, 3136(%r12)
	std %r9, 64(%r12)
	ld %r9, 3144(%r12)
	std %r9, 72(%r12)
	ld %r9, 3152(%r12)
	std %r9, 80(%r12)
	ld %r9, 3160(%r12)
	std %r9, 88(%r12)
	ld %r9, 3168(%r12)
	std %r9, 96(%r12)
	ld %r9, 3176(%r12)
	std %r9, 104(%r12)
	ld %r9, 3184(%r12)
	std %r9, 112(%r12)
	ld %r9, 3192(%r12)
	std %r9, 120(%r12)
	ld %r9, 3200(%r12)
	std %r9, 128(%r12)
	ld %r9, 3208(%r12)
	std %r9, 136(%r12)
	ld %r9, 3216(%r12)
	std %r9, 144(%r12)
	ld %r9, 3224(%r12)
	std %r9, 152(%r12)
	ld %r9, 3232(%r12)
	std %r9, 160(%r12)
	ld %r9, 3240(%r12)
	std %r9, 168(%r12)
	ld %r9, 3248(%r12)
	std %r9, 176(%r12)
	ld %r9, 3256(%r12)
	std %r9, 184(%r12)
	ld %r9, 3264(%r12)
	std %r9, 192(%r12)
	ld %r9, 3272(%r12)
	std %r9, 200(%r12)
	ld %r9, 3280(%r12)
	std %r9, 208(%r12)
	ld %r9, 3288(%r12)
	std %r9, 216(%r12)
	ld %r9, 3296(%r12)
	std %r9, 224(%r12)
	ld %r9, 3304(%r12)
	std %r9, 232(%r12)
	ld %r9, 3312(%r12)
	std %r9, 240(%r12)
	ld %r9, 3320(%r12)
	std %r9, 248(%r12)
	ld %r9, 3328(%r12)
	std %r9, 256(%r12)
	ld %r9, 3336(%r12)
	std %r9, 264(%r12)
	ld %r9, 3344(%r12)
	std %r9, 272(%r12)
	ld %r9, 3352(%r12)
	std %r9, 280(%r12)
	ld %r9, 3360(%r12)
	std %r9, 288(%r12)
	ld %r9, 3368(%r12)
	std %r9, 296(%r12)
	ld %r9, 3376(%r12)
	std %r9, 304(%r12)
	ld %r9, 3384(%r12)
	std %r9, 312(%r12)
	ld %r9, 3392(%r12)
	std %r9, 320(%r12)
	ld %r9, 3400(%r12)
	std %r9, 328(%r12)
	ld %r9, 3408(%r12)
	std %r9, 336(%r12)
	ld %r9, 3416(%r12)
	std %r9, 344(%r12)
	ld %r9, 3424(%r12)
	std %r9, 352(%r12)
	ld %r9, 3432(%r12)
	std %r9, 360(%r12)
	ld %r9, 3440(%r12)
	std %r9, 368(%r12)
	ld %r9, 3448(%r12)
	std %r9, 376(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	addi %r4, %r1, 96
	addi %r5, %r1, 448
	ld %r9, 160(%r11)
	add %r5, %r5, %r9
	ld %r6, 208(%r11)
23:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
	addi %r11, %r1, 0
	ld %r9, 160(%r11)
	ld %r10, 208(%r11)
	add %r9, %r9, %r10
	std %r9, 160(%r11)
	li %r10, 32
	subfc %r12, %r10, %r9
	subfe %r12, %r12, %r12
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	addi %r11, %r1, 0
	ld %r3, 200(%r11)
	ld %r4, 192(%r11)
	addi %r5, %r1, 304
	addi %r6, %r1, 448
	ld %r7, 176(%r11)
	bl {vg_ecdsa_secp256k1_sign_k}
	addi %r11, %r1, 0
	ld %r9, 168(%r11)
	addi %r9, %r9, -1
	std %r9, 168(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 24f
	li %r12, 0
	b 25f
24:
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 1
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 1
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r12, 1
25:
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	addi %r11, %r1, 0
	li %r12, 0
	std %r12, 32(%r11)
	std %r12, 40(%r11)
	std %r12, 48(%r11)
	std %r12, 56(%r11)
	std %r12, 64(%r11)
	std %r12, 72(%r11)
	std %r12, 80(%r11)
	std %r12, 88(%r11)
	std %r12, 96(%r11)
	std %r12, 104(%r11)
	std %r12, 112(%r11)
	std %r12, 120(%r11)
	std %r12, 128(%r11)
	std %r12, 136(%r11)
	std %r12, 144(%r11)
	std %r12, 152(%r11)
	std %r12, 232(%r11)
	std %r12, 240(%r11)
	std %r12, 248(%r11)
	std %r12, 256(%r11)
	std %r12, 264(%r11)
	std %r12, 272(%r11)
	std %r12, 280(%r11)
	std %r12, 288(%r11)
	std %r12, 296(%r11)
	std %r12, 304(%r11)
	std %r12, 312(%r11)
	std %r12, 320(%r11)
	std %r12, 328(%r11)
	std %r12, 336(%r11)
	std %r12, 344(%r11)
	std %r12, 352(%r11)
	std %r12, 360(%r11)
	std %r12, 368(%r11)
	std %r12, 376(%r11)
	std %r12, 384(%r11)
	std %r12, 392(%r11)
	std %r12, 400(%r11)
	std %r12, 408(%r11)
	std %r12, 416(%r11)
	std %r12, 424(%r11)
	std %r12, 432(%r11)
	std %r12, 440(%r11)
	std %r12, 448(%r11)
	std %r12, 456(%r11)
	std %r12, 464(%r11)
	std %r12, 472(%r11)
	std %r12, 480(%r11)
	std %r12, 488(%r11)
	std %r12, 496(%r11)
	std %r12, 504(%r11)
	std %r12, 512(%r11)
	std %r12, 520(%r11)
	std %r12, 528(%r11)
	std %r12, 536(%r11)
	std %r12, 544(%r11)
	std %r12, 552(%r11)
	std %r12, 560(%r11)
	std %r12, 568(%r11)
	std %r12, 576(%r11)
	std %r12, 584(%r11)
	addi %r1, %r1, 592
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
