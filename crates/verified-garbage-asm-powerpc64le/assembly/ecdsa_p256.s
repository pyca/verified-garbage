// The functions of `src/ecdsa_p256.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1056(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1064(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1072(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
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
	ldbrx %r8, %r5, %r9
	std %r8, 1120(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1128(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1136(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1144(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 72(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 76(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 80(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 84(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 88(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 92(%r3)
	lis %r11, -925
	ori %r11, %r11, 9553
	stw %r11, 96(%r3)
	lis %r11, -3143
	ori %r11, %r11, 51906
	stw %r11, 100(%r3)
	lis %r11, -22761
	ori %r11, %r11, 40580
	stw %r11, 104(%r3)
	lis %r11, -17178
	ori %r11, %r11, 64173
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 1
	stw %r11, 224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 232(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 236(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 240(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 244(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 252(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 256(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 260(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 264(%r3)
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 276(%r3)
	lis %r11, 0
	ori %r11, %r11, 4
	stw %r11, 280(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 284(%r3)
	lis %r11, 32078
	ori %r11, %r11, 14751
	stw %r11, 288(%r3)
	lis %r11, -30250
	ori %r11, %r11, 40486
	stw %r11, 292(%r3)
	lis %r11, 27020
	ori %r11, %r11, 37298
	stw %r11, 296(%r3)
	lis %r11, 1744
	ori %r11, %r11, 4454
	stw %r11, 300(%r3)
	lis %r11, -6813
	ori %r11, %r11, 35972
	stw %r11, 304(%r3)
	lis %r11, -20250
	ori %r11, %r11, 25091
	stw %r11, 308(%r3)
	lis %r11, 3477
	ori %r11, %r11, 55452
	stw %r11, 312(%r3)
	lis %r11, -27504
	ori %r11, %r11, 4697
	stw %r11, 316(%r3)
	lis %r11, 6313
	ori %r11, %r11, 5180
	stw %r11, 320(%r3)
	lis %r11, 31207
	ori %r11, %r11, 12500
	stw %r11, 324(%r3)
	lis %r11, 24557
	ori %r11, %r11, 46593
	stw %r11, 328(%r3)
	lis %r11, 30138
	ori %r11, %r11, 38396
	stw %r11, 332(%r3)
	lis %r11, 30562
	ori %r11, %r11, 9488
	stw %r11, 336(%r3)
	lis %r11, 31227
	ori %r11, %r11, 29483
	stw %r11, 340(%r3)
	lis %r11, -23241
	ori %r11, %r11, 21958
	stw %r11, 344(%r3)
	lis %r11, 6288
	ori %r11, %r11, 24438
	stw %r11, 348(%r3)
	lis %r11, -12651
	ori %r11, %r11, 22026
	stw %r11, 352(%r3)
	lis %r11, -8718
	ori %r11, %r11, 21335
	stw %r11, 356(%r3)
	lis %r11, -17895
	ori %r11, %r11, 58460
	stw %r11, 360(%r3)
	lis %r11, -29878
	ori %r11, %r11, 47332
	stw %r11, 364(%r3)
	lis %r11, -8927
	ori %r11, %r11, 62245
	stw %r11, 368(%r3)
	lis %r11, -11544
	ori %r11, %r11, 34440
	stw %r11, 372(%r3)
	lis %r11, 9608
	ori %r11, %r11, 23941
	stw %r11, 376(%r3)
	lis %r11, -31375
	ori %r11, %r11, 65304
	stw %r11, 380(%r3)
	lis %r11, -16775
	ori %r11, %r11, 61090
	stw %r11, 384(%r3)
	lis %r11, -31964
	ori %r11, %r11, 19605
	stw %r11, 388(%r3)
	lis %r11, 18877
	ori %r11, %r11, 28582
	stw %r11, 392(%r3)
	lis %r11, 18073
	ori %r11, %r11, 31132
	stw %r11, 396(%r3)
	lis %r11, 11115
	ori %r11, %r11, 60505
	stw %r11, 400(%r3)
	lis %r11, 10309
	ori %r11, %r11, 45625
	stw %r11, 404(%r3)
	lis %r11, -3111
	ori %r11, %r11, 22048
	stw %r11, 408(%r3)
	lis %r11, 26337
	ori %r11, %r11, 11668
	stw %r11, 412(%r3)
	lis %r11, 924
	ori %r11, %r11, 55983
	stw %r11, 416(%r3)
	lis %r11, 3142
	ori %r11, %r11, 13629
	stw %r11, 420(%r3)
	lis %r11, 22760
	ori %r11, %r11, 24955
	stw %r11, 424(%r3)
	lis %r11, 17177
	ori %r11, %r11, 1362
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 452(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 464(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 468(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 472(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 476(%r3)
	lis %r11, -925
	ori %r11, %r11, 9551
	stw %r11, 480(%r3)
	lis %r11, -3143
	ori %r11, %r11, 51906
	stw %r11, 484(%r3)
	lis %r11, -22761
	ori %r11, %r11, 40580
	stw %r11, 488(%r3)
	lis %r11, -17178
	ori %r11, %r11, 64173
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 1
	stw %r11, 544(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 548(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 560(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 564(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	ld %r4, 320(%r3)
	std %r4, 512(%r3)
	ld %r4, 328(%r3)
	std %r4, 520(%r3)
	ld %r4, 336(%r3)
	std %r4, 528(%r3)
	ld %r4, 344(%r3)
	std %r4, 536(%r3)
	ld %r4, 352(%r3)
	std %r4, 544(%r3)
	ld %r4, 360(%r3)
	std %r4, 552(%r3)
	ld %r4, 368(%r3)
	std %r4, 560(%r3)
	ld %r4, 376(%r3)
	std %r4, 568(%r3)
	bl {vg_p256_mul}
	ld %r4, 224(%r3)
	std %r4, 992(%r3)
	ld %r4, 232(%r3)
	std %r4, 1000(%r3)
	ld %r4, 240(%r3)
	std %r4, 1008(%r3)
	ld %r4, 248(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
23:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 576
	bl {vg_p256_mul_mod_p}
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
	bne %cr0, 23b
	li %r4, 1152
	li %r5, 512
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	li %r4, 1184
	li %r5, 1152
	li %r6, 192
	bl {vg_p256_mul_mod_p}
	li %r4, 1216
	li %r5, 1184
	li %r6, 160
	bl {vg_p256_add_mod_n}
	li %r4, 1248
	li %r5, 1056
	li %r6, 384
	bl {vg_p256_mul_mod_n}
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
	ld %r5, 1216(%r3)
	ld %r4, 1224(%r3)
	or %r5, %r5, %r4
	ld %r4, 1232(%r3)
	or %r5, %r5, %r4
	ld %r4, 1240(%r3)
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
	ld %r4, 416(%r3)
	std %r4, 992(%r3)
	ld %r4, 424(%r3)
	std %r4, 1000(%r3)
	ld %r4, 432(%r3)
	std %r4, 1008(%r3)
	ld %r4, 440(%r3)
	std %r4, 1016(%r3)
	li %r31, 256
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 1024
	li %r5, 992
	li %r6, 1248
	bl {vg_p256_mul_mod_n}
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
	bne %cr0, 24b
	li %r4, 1280
	li %r5, 1216
	li %r6, 384
	bl {vg_p256_mul_mod_n}
	li %r4, 1312
	li %r5, 1088
	li %r6, 384
	bl {vg_p256_mul_mod_n}
	li %r4, 1344
	li %r5, 1120
	li %r6, 384
	bl {vg_p256_mul_mod_n}
	li %r4, 1376
	li %r5, 1280
	li %r6, 1312
	bl {vg_p256_mul_mod_n}
	li %r4, 1376
	li %r5, 1376
	li %r6, 1344
	bl {vg_p256_add_mod_n}
	li %r4, 1408
	li %r5, 992
	li %r6, 1376
	bl {vg_p256_mul_mod_n}
	li %r4, 1440
	li %r5, 1408
	li %r6, 192
	bl {vg_p256_mul_mod_n}
	ld %r5, 1440(%r3)
	ld %r4, 1448(%r3)
	or %r5, %r5, %r4
	ld %r4, 1456(%r3)
	or %r5, %r5, %r4
	ld %r4, 1464(%r3)
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
	ld %r4, 1216(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1224(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1232(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1240(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 1440(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 1448(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 1456(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 1464(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ecdsa_p256_verify:
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
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 72(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 76(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 80(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 84(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 88(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 92(%r3)
	lis %r11, -925
	ori %r11, %r11, 9553
	stw %r11, 96(%r3)
	lis %r11, -3143
	ori %r11, %r11, 51906
	stw %r11, 100(%r3)
	lis %r11, -22761
	ori %r11, %r11, 40580
	stw %r11, 104(%r3)
	lis %r11, -17178
	ori %r11, %r11, 64173
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 1
	stw %r11, 224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 232(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 236(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 240(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 244(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 252(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 256(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 260(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 264(%r3)
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 276(%r3)
	lis %r11, 0
	ori %r11, %r11, 4
	stw %r11, 280(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 284(%r3)
	lis %r11, 32078
	ori %r11, %r11, 14751
	stw %r11, 288(%r3)
	lis %r11, -30250
	ori %r11, %r11, 40486
	stw %r11, 292(%r3)
	lis %r11, 27020
	ori %r11, %r11, 37298
	stw %r11, 296(%r3)
	lis %r11, 1744
	ori %r11, %r11, 4454
	stw %r11, 300(%r3)
	lis %r11, -6813
	ori %r11, %r11, 35972
	stw %r11, 304(%r3)
	lis %r11, -20250
	ori %r11, %r11, 25091
	stw %r11, 308(%r3)
	lis %r11, 3477
	ori %r11, %r11, 55452
	stw %r11, 312(%r3)
	lis %r11, -27504
	ori %r11, %r11, 4697
	stw %r11, 316(%r3)
	lis %r11, 6313
	ori %r11, %r11, 5180
	stw %r11, 320(%r3)
	lis %r11, 31207
	ori %r11, %r11, 12500
	stw %r11, 324(%r3)
	lis %r11, 24557
	ori %r11, %r11, 46593
	stw %r11, 328(%r3)
	lis %r11, 30138
	ori %r11, %r11, 38396
	stw %r11, 332(%r3)
	lis %r11, 30562
	ori %r11, %r11, 9488
	stw %r11, 336(%r3)
	lis %r11, 31227
	ori %r11, %r11, 29483
	stw %r11, 340(%r3)
	lis %r11, -23241
	ori %r11, %r11, 21958
	stw %r11, 344(%r3)
	lis %r11, 6288
	ori %r11, %r11, 24438
	stw %r11, 348(%r3)
	lis %r11, -12651
	ori %r11, %r11, 22026
	stw %r11, 352(%r3)
	lis %r11, -8718
	ori %r11, %r11, 21335
	stw %r11, 356(%r3)
	lis %r11, -17895
	ori %r11, %r11, 58460
	stw %r11, 360(%r3)
	lis %r11, -29878
	ori %r11, %r11, 47332
	stw %r11, 364(%r3)
	lis %r11, -8927
	ori %r11, %r11, 62245
	stw %r11, 368(%r3)
	lis %r11, -11544
	ori %r11, %r11, 34440
	stw %r11, 372(%r3)
	lis %r11, 9608
	ori %r11, %r11, 23941
	stw %r11, 376(%r3)
	lis %r11, -31375
	ori %r11, %r11, 65304
	stw %r11, 380(%r3)
	lis %r11, -16775
	ori %r11, %r11, 61090
	stw %r11, 384(%r3)
	lis %r11, -31964
	ori %r11, %r11, 19605
	stw %r11, 388(%r3)
	lis %r11, 18877
	ori %r11, %r11, 28582
	stw %r11, 392(%r3)
	lis %r11, 18073
	ori %r11, %r11, 31132
	stw %r11, 396(%r3)
	lis %r11, 11115
	ori %r11, %r11, 60505
	stw %r11, 400(%r3)
	lis %r11, 10309
	ori %r11, %r11, 45625
	stw %r11, 404(%r3)
	lis %r11, -3111
	ori %r11, %r11, 22048
	stw %r11, 408(%r3)
	lis %r11, 26337
	ori %r11, %r11, 11668
	stw %r11, 412(%r3)
	lis %r11, 924
	ori %r11, %r11, 55983
	stw %r11, 416(%r3)
	lis %r11, 3142
	ori %r11, %r11, 13629
	stw %r11, 420(%r3)
	lis %r11, 22760
	ori %r11, %r11, 24955
	stw %r11, 424(%r3)
	lis %r11, 17177
	ori %r11, %r11, 1362
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 448(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 452(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 464(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 468(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 472(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 476(%r3)
	lis %r11, -925
	ori %r11, %r11, 9551
	stw %r11, 480(%r3)
	lis %r11, -3143
	ori %r11, %r11, 51906
	stw %r11, 484(%r3)
	lis %r11, -22761
	ori %r11, %r11, 40580
	stw %r11, 488(%r3)
	lis %r11, -17178
	ori %r11, %r11, 64173
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	ori %r11, %r11, 1
	stw %r11, 544(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 548(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 560(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 564(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 1312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1316(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1320(%r3)
	lis %r11, -1
	ori %r11, %r11, 65531
	stw %r11, 1324(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1328(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1332(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 1336(%r3)
	lis %r11, 0
	ori %r11, %r11, 4
	stw %r11, 1340(%r3)
	lis %r11, 10692
	ori %r11, %r11, 48607
	stw %r11, 1344(%r3)
	lis %r11, -10084
	ori %r11, %r11, 57186
	stw %r11, 1348(%r3)
	lis %r11, 30852
	ori %r11, %r11, 12432
	stw %r11, 1352(%r3)
	lis %r11, -21264
	ori %r11, %r11, 1485
	stw %r11, 1356(%r3)
	lis %r11, -2271
	ori %r11, %r11, 11990
	stw %r11, 1360(%r3)
	lis %r11, -6750
	ori %r11, %r11, 8363
	stw %r11, 1364(%r3)
	lis %r11, 1159
	ori %r11, %r11, 18484
	stw %r11, 1368(%r3)
	lis %r11, -9168
	ori %r11, %r11, 1565
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
	bl {vg_p256_mul_mod_p}
	li %r4, 1184
	li %r5, 1216
	li %r6, 1312
	bl {vg_p256_mul_mod_p}
	li %r4, 1248
	li %r5, 1184
	li %r6, 1184
	bl {vg_p256_mul_mod_p}
	li %r4, 1376
	li %r5, 1152
	li %r6, 1152
	bl {vg_p256_mul_mod_p}
	li %r4, 1408
	li %r5, 1376
	li %r6, 1152
	bl {vg_p256_mul_mod_p}
	li %r4, 1376
	li %r5, 256
	li %r6, 1152
	bl {vg_p256_mul_mod_p}
	li %r4, 1280
	li %r5, 1408
	li %r6, 1376
	bl {vg_p256_add_mod_p}
	li %r4, 1408
	li %r5, 1280
	li %r6, 1344
	bl {vg_p256_add_mod_p}
	li %r4, 1376
	li %r5, 1248
	li %r6, 1408
	bl {vg_p256_sub_mod_p}
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
	bl {vg_p256_mul_mod_n}
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
	bl {vg_p256_mul_mod_n}
	li %r4, 1024
	li %r5, 992
	li %r6, 1248
	bl {vg_p256_mul_mod_n}
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
	bl {vg_p256_mul_mod_n}
	li %r4, 1312
	li %r5, 1056
	li %r6, 384
	bl {vg_p256_mul_mod_n}
	li %r4, 1376
	li %r5, 1344
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 1408
	li %r5, 1312
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	li %r4, 1152
	li %r5, 1376
	li %r6, 192
	bl {vg_p256_mul_mod_n}
	li %r4, 1184
	li %r5, 1408
	li %r6, 192
	bl {vg_p256_mul_mod_n}
	ld %r4, 1152(%r3)
	std %r4, 1056(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1064(%r3)
	ld %r4, 1168(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1176(%r3)
	std %r4, 1080(%r3)
	ld %r4, 320(%r3)
	std %r4, 512(%r3)
	ld %r4, 328(%r3)
	std %r4, 520(%r3)
	ld %r4, 336(%r3)
	std %r4, 528(%r3)
	ld %r4, 344(%r3)
	std %r4, 536(%r3)
	ld %r4, 352(%r3)
	std %r4, 544(%r3)
	ld %r4, 360(%r3)
	std %r4, 552(%r3)
	ld %r4, 368(%r3)
	std %r4, 560(%r3)
	ld %r4, 376(%r3)
	std %r4, 568(%r3)
	bl {vg_p256_mul}
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
	ori %r11, %r11, 1
	stw %r11, 544(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 548(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 560(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 564(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	ld %r4, 1184(%r3)
	std %r4, 1056(%r3)
	ld %r4, 1192(%r3)
	std %r4, 1064(%r3)
	ld %r4, 1200(%r3)
	std %r4, 1072(%r3)
	ld %r4, 1208(%r3)
	std %r4, 1080(%r3)
	ld %r4, 1280(%r3)
	std %r4, 512(%r3)
	ld %r4, 1288(%r3)
	std %r4, 520(%r3)
	ld %r4, 1296(%r3)
	std %r4, 528(%r3)
	ld %r4, 1304(%r3)
	std %r4, 536(%r3)
	ld %r4, 1440(%r3)
	std %r4, 544(%r3)
	ld %r4, 1448(%r3)
	std %r4, 552(%r3)
	ld %r4, 1456(%r3)
	std %r4, 560(%r3)
	ld %r4, 1464(%r3)
	std %r4, 568(%r3)
	bl {vg_p256_mul}
	li %r4, 800
	li %r5, 1376
	li %r6, 512
	bl {vg_p256_mul_mod_p}
	li %r4, 832
	li %r5, 1408
	li %r6, 544
	bl {vg_p256_mul_mod_p}
	li %r4, 864
	li %r5, 1248
	li %r6, 576
	bl {vg_p256_mul_mod_p}
	li %r4, 896
	li %r5, 1376
	li %r6, 1408
	bl {vg_p256_add_mod_p}
	li %r4, 928
	li %r5, 512
	li %r6, 544
	bl {vg_p256_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p256_mul_mod_p}
	li %r4, 928
	li %r5, 800
	li %r6, 832
	bl {vg_p256_add_mod_p}
	li %r4, 896
	li %r5, 896
	li %r6, 928
	bl {vg_p256_sub_mod_p}
	li %r4, 928
	li %r5, 1376
	li %r6, 1248
	bl {vg_p256_add_mod_p}
	li %r4, 960
	li %r5, 512
	li %r6, 576
	bl {vg_p256_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_p256_mul_mod_p}
	li %r4, 960
	li %r5, 800
	li %r6, 864
	bl {vg_p256_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 960
	bl {vg_p256_sub_mod_p}
	li %r4, 960
	li %r5, 1408
	li %r6, 1248
	bl {vg_p256_add_mod_p}
	li %r4, 608
	li %r5, 544
	li %r6, 576
	bl {vg_p256_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_p256_mul_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 864
	bl {vg_p256_add_mod_p}
	li %r4, 960
	li %r5, 960
	li %r6, 608
	bl {vg_p256_sub_mod_p}
	li %r4, 672
	li %r5, 256
	li %r6, 928
	bl {vg_p256_mul_mod_p}
	li %r4, 608
	li %r5, 288
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 672
	li %r5, 608
	li %r6, 672
	bl {vg_p256_add_mod_p}
	li %r4, 608
	li %r5, 832
	li %r6, 672
	bl {vg_p256_sub_mod_p}
	li %r4, 672
	li %r5, 832
	li %r6, 672
	bl {vg_p256_add_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 672
	bl {vg_p256_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 800
	bl {vg_p256_add_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 800
	bl {vg_p256_add_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 928
	li %r5, 288
	li %r6, 928
	bl {vg_p256_mul_mod_p}
	li %r4, 832
	li %r5, 832
	li %r6, 864
	bl {vg_p256_add_mod_p}
	li %r4, 864
	li %r5, 800
	li %r6, 864
	bl {vg_p256_sub_mod_p}
	li %r4, 864
	li %r5, 256
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 864
	bl {vg_p256_add_mod_p}
	li %r4, 800
	li %r5, 832
	li %r6, 928
	bl {vg_p256_mul_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 800
	bl {vg_p256_add_mod_p}
	li %r4, 800
	li %r5, 960
	li %r6, 928
	bl {vg_p256_mul_mod_p}
	li %r4, 608
	li %r5, 896
	li %r6, 608
	bl {vg_p256_mul_mod_p}
	li %r4, 608
	li %r5, 608
	li %r6, 800
	bl {vg_p256_sub_mod_p}
	li %r4, 800
	li %r5, 896
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r4, 672
	li %r5, 960
	li %r6, 672
	bl {vg_p256_mul_mod_p}
	li %r4, 672
	li %r5, 672
	li %r6, 800
	bl {vg_p256_add_mod_p}
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
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	li %r4, 1024
	li %r5, 992
	li %r6, 576
	bl {vg_p256_mul_mod_p}
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
	bl {vg_p256_mul_mod_p}
	li %r4, 1184
	li %r5, 1152
	li %r6, 192
	bl {vg_p256_mul_mod_p}
	li %r4, 1280
	li %r5, 1184
	li %r6, 384
	bl {vg_p256_mul_mod_n}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1312
	bl {vg_p256_sub_mod_n}
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
