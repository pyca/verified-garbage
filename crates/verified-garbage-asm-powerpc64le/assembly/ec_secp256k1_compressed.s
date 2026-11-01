// The functions of `src/ec_secp256k1_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_secp256k1_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1056(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1064(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1080(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1088(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1096(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1104(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1112(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1120(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1128(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
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
	addi %r6, %r12, 1
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
	ld %r10, 1472(%r3)
	ld %r4, 1216(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1120(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1128(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1136(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1144(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ec_secp256k1_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1056(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1064(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1080(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1088(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1096(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1104(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 1112(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 1120(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 1128(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
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
	addi %r6, %r12, 1
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
	lbz %r4, 0(%r12)
	std %r4, 1088(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
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
	li %r4, 1152
	li %r5, 1120
	li %r6, 1312
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
	lis %r11, -16385
	ori %r11, %r11, 65292
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	lis %r11, 16383
	ori %r11, %r11, 65535
	stw %r11, 476(%r3)
	li %r31, 32
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 448(%r4)
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
	bne %cr0, 20b
	ld %r4, 224(%r3)
	std %r4, 992(%r3)
	ld %r4, 232(%r3)
	std %r4, 1000(%r3)
	ld %r4, 240(%r3)
	std %r4, 1008(%r3)
	ld %r4, 248(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
21:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 1408
	bl {vg_secp256k1_mul_mod_p}
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
	bne %cr0, 21b
	li %r4, 1216
	li %r5, 992
	li %r6, 192
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1248
	li %r5, 160
	li %r6, 1216
	bl {vg_secp256k1_sub_mod_p}
	ld %r4, 1216(%r3)
	ld %r5, 1088(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 1216(%r3)
	ld %r5, 1248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1216(%r3)
	ld %r4, 1224(%r3)
	ld %r5, 1256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1224(%r3)
	ld %r4, 1232(%r3)
	ld %r5, 1264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1232(%r3)
	ld %r4, 1240(%r3)
	ld %r5, 1272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1240(%r3)
	li %r4, 1184
	li %r5, 1216
	li %r6, 1312
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1376
	li %r5, 1184
	li %r6, 1184
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 1280
	li %r5, 1376
	li %r6, 1408
	bl {vg_secp256k1_sub_mod_p}
	ld %r5, 1280(%r3)
	ld %r4, 1288(%r3)
	or %r5, %r5, %r4
	ld %r4, 1296(%r3)
	or %r5, %r5, %r4
	ld %r4, 1304(%r3)
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
	ld %r4, 1216(%r3)
	ld %r5, 1088(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 1472(%r3)
	and %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r10, 1472(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 1120(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 1128(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 1136(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 1144(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 1216(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 1224(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 1232(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 1240(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
