// The functions of `src/internal/vg_ecdsa_p256_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign_k:
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
	ld %r4, 576(%r3)
	std %r4, 608(%r3)
	ld %r4, 584(%r3)
	std %r4, 616(%r3)
	ld %r4, 592(%r3)
	std %r4, 624(%r3)
	ld %r4, 600(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 576
	li %r6, 576
	bl {vg_p256_mul_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_p256_mul_mod_p}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
25:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
27:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 32
210:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p256_mul_mod_p}
	li %r31, 100
211:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
212:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
213:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
214:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
215:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
216:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
217:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
218:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
221:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
222:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
223:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
224:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
226:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
227:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
229:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
230:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
231:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
232:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_p}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 992
	li %r5, 992
	li %r6, 800
	bl {vg_p256_mul_mod_p}
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
	ld %r4, 1248(%r3)
	std %r4, 608(%r3)
	ld %r4, 1256(%r3)
	std %r4, 616(%r3)
	ld %r4, 1264(%r3)
	std %r4, 624(%r3)
	ld %r4, 1272(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 1248
	li %r6, 1248
	bl {vg_p256_mul_mod_n}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_p256_mul_mod_n}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 4
235:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
236:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
237:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
238:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
239:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
240:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
241:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 36
242:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
243:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
244:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
245:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
246:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
247:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
248:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
249:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
250:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
251:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
252:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
254:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
255:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
256:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
257:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
258:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 2
259:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 5
260:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 6
261:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 992
	li %r5, 992
	li %r6, 800
	bl {vg_p256_mul_mod_n}
	li %r31, 4
262:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 4
263:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 5
264:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 5
265:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 992
	li %r5, 992
	li %r6, 800
	bl {vg_p256_mul_mod_n}
	li %r31, 5
266:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 7
267:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 2
268:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 6
269:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 2
270:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_p256_mul_mod_n}
	li %r31, 8
271:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p256_mul_mod_n}
	li %r31, 3
272:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
273:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 4
274:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
275:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_p256_mul_mod_n}
	li %r31, 5
276:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 3
277:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 8
278:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_p256_mul_mod_n}
	li %r31, 4
279:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
	li %r31, 5
280:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 5
281:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_p256_mul_mod_n}
	li %r31, 6
282:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 992
	li %r5, 992
	li %r6, 736
	bl {vg_p256_mul_mod_n}
	li %r31, 4
283:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 992
	li %r5, 992
	li %r6, 672
	bl {vg_p256_mul_mod_n}
	li %r31, 6
284:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_p256_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_p256_mul_mod_n}
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
