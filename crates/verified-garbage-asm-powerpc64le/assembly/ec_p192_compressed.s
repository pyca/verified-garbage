// The functions of `src/ec_p192_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 808(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 816(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 824(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 832(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 840(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 848(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 872(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	lis %r11, -19246
	ori %r11, %r11, 10289
	stw %r11, 88(%r3)
	lis %r11, 5227
	ori %r11, %r11, 51633
	stw %r11, 92(%r3)
	lis %r11, -26146
	ori %r11, %r11, 63542
	stw %r11, 96(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 100(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 108(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 144(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 148(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 152(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 156(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
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
	ori %r11, %r11, 1
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
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 208(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 212(%r3)
	lis %r11, -1
	ori %r11, %r11, 65531
	stw %r11, 216(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 220(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 224(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 228(%r3)
	lis %r11, -2903
	ori %r11, %r11, 45001
	stw %r11, 232(%r3)
	lis %r11, 10381
	ori %r11, %r11, 44051
	stw %r11, 236(%r3)
	lis %r11, 19222
	ori %r11, %r11, 16552
	stw %r11, 240(%r3)
	lis %r11, 22405
	ori %r11, %r11, 26902
	stw %r11, 244(%r3)
	lis %r11, 1858
	ori %r11, %r11, 5012
	stw %r11, 248(%r3)
	lis %r11, 23386
	ori %r11, %r11, 52304
	stw %r11, 252(%r3)
	lis %r11, 13103
	ori %r11, %r11, 41224
	stw %r11, 256(%r3)
	lis %r11, 3468
	ori %r11, %r11, 45836
	stw %r11, 260(%r3)
	lis %r11, 30417
	ori %r11, %r11, 10505
	stw %r11, 264(%r3)
	lis %r11, -30133
	ori %r11, %r11, 54263
	stw %r11, 268(%r3)
	lis %r11, -3118
	ori %r11, %r11, 6391
	stw %r11, 272(%r3)
	lis %r11, -27316
	ori %r11, %r11, 51449
	stw %r11, 276(%r3)
	lis %r11, 7746
	ori %r11, %r11, 8841
	stw %r11, 280(%r3)
	lis %r11, 31506
	ori %r11, %r11, 41783
	stw %r11, 284(%r3)
	lis %r11, -30362
	ori %r11, %r11, 61534
	stw %r11, 288(%r3)
	lis %r11, -8670
	ori %r11, %r11, 46372
	stw %r11, 292(%r3)
	lis %r11, 27373
	ori %r11, %r11, 43085
	stw %r11, 296(%r3)
	lis %r11, 27177
	ori %r11, %r11, 15747
	stw %r11, 300(%r3)
	lis %r11, -8525
	ori %r11, %r11, 22881
	stw %r11, 304(%r3)
	lis %r11, -12698
	ori %r11, %r11, 47820
	stw %r11, 308(%r3)
	lis %r11, -17606
	ori %r11, %r11, 27630
	stw %r11, 312(%r3)
	lis %r11, 18070
	ori %r11, %r11, 59995
	stw %r11, 316(%r3)
	lis %r11, -5627
	ori %r11, %r11, 33186
	stw %r11, 320(%r3)
	lis %r11, 10430
	ori %r11, %r11, 22135
	stw %r11, 324(%r3)
	lis %r11, 19245
	ori %r11, %r11, 55247
	stw %r11, 328(%r3)
	lis %r11, -5228
	ori %r11, %r11, 13902
	stw %r11, 332(%r3)
	lis %r11, 26145
	ori %r11, %r11, 1993
	stw %r11, 336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 340(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 352(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 356(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 360(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 364(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 368(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 372(%r3)
	lis %r11, -19246
	ori %r11, %r11, 10287
	stw %r11, 376(%r3)
	lis %r11, 5227
	ori %r11, %r11, 51633
	stw %r11, 380(%r3)
	lis %r11, -26146
	ori %r11, %r11, 63542
	stw %r11, 384(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 388(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 392(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 396(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 400(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 404(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 420(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 424(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 448(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 452(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1120(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1000(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1004(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1012(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1016(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1020(%r3)
	lis %r11, -22813
	ori %r11, %r11, 15000
	stw %r11, 1024(%r3)
	lis %r11, 25305
	ori %r11, %r11, 58374
	stw %r11, 1028(%r3)
	lis %r11, 6407
	ori %r11, %r11, 27362
	stw %r11, 1032(%r3)
	lis %r11, 29313
	ori %r11, %r11, 52658
	stw %r11, 1036(%r3)
	lis %r11, 22464
	ori %r11, %r11, 45361
	stw %r11, 1040(%r3)
	lis %r11, 29640
	ori %r11, %r11, 61125
	stw %r11, 1044(%r3)
	addi %r6, %r12, 1
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 872(%r3)
	addi %r6, %r6, 24
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 928(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 936(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 944(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 856(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 860(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 864(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 868(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 872(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 876(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 928(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 932(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 936(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 940(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 944(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 948(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r4, 880
	li %r5, 856
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 904
	li %r5, 928
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 952
	li %r5, 904
	li %r6, 904
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 880
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1072
	li %r5, 1048
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 208
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1048
	bl {vg_p192_add_mod_p}
	li %r4, 1072
	li %r5, 976
	li %r6, 1024
	bl {vg_p192_add_mod_p}
	li %r4, 1048
	li %r5, 952
	li %r6, 1072
	bl {vg_p192_sub_mod_p}
	ld %r5, 1048(%r3)
	ld %r4, 1056(%r3)
	or %r5, %r5, %r4
	ld %r4, 1064(%r3)
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
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r10, 1120(%r3)
	ld %r4, 256(%r3)
	ld %r5, 880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 264(%r3)
	ld %r5, 888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 272(%r3)
	ld %r5, 896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 280(%r3)
	ld %r5, 904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1096(%r3)
	ld %r4, 288(%r3)
	ld %r5, 912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1104(%r3)
	ld %r4, 296(%r3)
	ld %r5, 920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1112(%r3)
	ld %r10, 1120(%r3)
	ld %r4, 928(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 856(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 864(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 872(%r3)
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

vg_ec_p192_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 808(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 816(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 824(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 832(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 840(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 848(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 872(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	lis %r11, -19246
	ori %r11, %r11, 10289
	stw %r11, 88(%r3)
	lis %r11, 5227
	ori %r11, %r11, 51633
	stw %r11, 92(%r3)
	lis %r11, -26146
	ori %r11, %r11, 63542
	stw %r11, 96(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 100(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 108(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 144(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 148(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 152(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 156(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
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
	ori %r11, %r11, 1
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
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 208(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 212(%r3)
	lis %r11, -1
	ori %r11, %r11, 65531
	stw %r11, 216(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 220(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 224(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 228(%r3)
	lis %r11, -2903
	ori %r11, %r11, 45001
	stw %r11, 232(%r3)
	lis %r11, 10381
	ori %r11, %r11, 44051
	stw %r11, 236(%r3)
	lis %r11, 19222
	ori %r11, %r11, 16552
	stw %r11, 240(%r3)
	lis %r11, 22405
	ori %r11, %r11, 26902
	stw %r11, 244(%r3)
	lis %r11, 1858
	ori %r11, %r11, 5012
	stw %r11, 248(%r3)
	lis %r11, 23386
	ori %r11, %r11, 52304
	stw %r11, 252(%r3)
	lis %r11, 13103
	ori %r11, %r11, 41224
	stw %r11, 256(%r3)
	lis %r11, 3468
	ori %r11, %r11, 45836
	stw %r11, 260(%r3)
	lis %r11, 30417
	ori %r11, %r11, 10505
	stw %r11, 264(%r3)
	lis %r11, -30133
	ori %r11, %r11, 54263
	stw %r11, 268(%r3)
	lis %r11, -3118
	ori %r11, %r11, 6391
	stw %r11, 272(%r3)
	lis %r11, -27316
	ori %r11, %r11, 51449
	stw %r11, 276(%r3)
	lis %r11, 7746
	ori %r11, %r11, 8841
	stw %r11, 280(%r3)
	lis %r11, 31506
	ori %r11, %r11, 41783
	stw %r11, 284(%r3)
	lis %r11, -30362
	ori %r11, %r11, 61534
	stw %r11, 288(%r3)
	lis %r11, -8670
	ori %r11, %r11, 46372
	stw %r11, 292(%r3)
	lis %r11, 27373
	ori %r11, %r11, 43085
	stw %r11, 296(%r3)
	lis %r11, 27177
	ori %r11, %r11, 15747
	stw %r11, 300(%r3)
	lis %r11, -8525
	ori %r11, %r11, 22881
	stw %r11, 304(%r3)
	lis %r11, -12698
	ori %r11, %r11, 47820
	stw %r11, 308(%r3)
	lis %r11, -17606
	ori %r11, %r11, 27630
	stw %r11, 312(%r3)
	lis %r11, 18070
	ori %r11, %r11, 59995
	stw %r11, 316(%r3)
	lis %r11, -5627
	ori %r11, %r11, 33186
	stw %r11, 320(%r3)
	lis %r11, 10430
	ori %r11, %r11, 22135
	stw %r11, 324(%r3)
	lis %r11, 19245
	ori %r11, %r11, 55247
	stw %r11, 328(%r3)
	lis %r11, -5228
	ori %r11, %r11, 13902
	stw %r11, 332(%r3)
	lis %r11, 26145
	ori %r11, %r11, 1993
	stw %r11, 336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 340(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 352(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 356(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 360(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 364(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 368(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 372(%r3)
	lis %r11, -19246
	ori %r11, %r11, 10287
	stw %r11, 376(%r3)
	lis %r11, 5227
	ori %r11, %r11, 51633
	stw %r11, 380(%r3)
	lis %r11, -26146
	ori %r11, %r11, 63542
	stw %r11, 384(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 388(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 392(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 396(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 400(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 404(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 420(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 424(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 448(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 452(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1120(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1000(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1004(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1012(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1016(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1020(%r3)
	lis %r11, -22813
	ori %r11, %r11, 15000
	stw %r11, 1024(%r3)
	lis %r11, 25305
	ori %r11, %r11, 58374
	stw %r11, 1028(%r3)
	lis %r11, 6407
	ori %r11, %r11, 27362
	stw %r11, 1032(%r3)
	lis %r11, 29313
	ori %r11, %r11, 52658
	stw %r11, 1036(%r3)
	lis %r11, 22464
	ori %r11, %r11, 45361
	stw %r11, 1040(%r3)
	lis %r11, 29640
	ori %r11, %r11, 61125
	stw %r11, 1044(%r3)
	addi %r6, %r12, 1
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 872(%r3)
	lbz %r4, 0(%r12)
	std %r4, 832(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 856(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 860(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 864(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 868(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 872(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 876(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r4, 880
	li %r5, 856
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 880
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1072
	li %r5, 1048
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 208
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1048
	bl {vg_p192_add_mod_p}
	li %r4, 1072
	li %r5, 976
	li %r6, 1024
	bl {vg_p192_add_mod_p}
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 352(%r3)
	lis %r11, -16384
	ori %r11, %r11, 0
	stw %r11, 356(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 360(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 364(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 368(%r3)
	lis %r11, 16383
	ori %r11, %r11, 65535
	stw %r11, 372(%r3)
	li %r31, 24
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 352(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4480(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4481(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4482(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4483(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4484(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4485(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4486(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4487(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	ld %r4, 184(%r3)
	std %r4, 760(%r3)
	ld %r4, 192(%r3)
	std %r4, 768(%r3)
	ld %r4, 200(%r3)
	std %r4, 776(%r3)
	li %r31, 192
21:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 784
	li %r5, 760
	li %r6, 1072
	bl {vg_p192_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4480(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 760(%r3)
	ld %r5, 784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 768(%r3)
	ld %r5, 792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 776(%r3)
	ld %r5, 800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 928
	li %r5, 760
	li %r6, 160
	bl {vg_p192_mul_mod_p}
	li %r4, 952
	li %r5, 136
	li %r6, 928
	bl {vg_p192_sub_mod_p}
	ld %r4, 928(%r3)
	ld %r5, 832(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 928(%r3)
	ld %r5, 952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	li %r4, 904
	li %r5, 928
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 904
	li %r6, 904
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 1048
	li %r6, 1072
	bl {vg_p192_sub_mod_p}
	ld %r5, 976(%r3)
	ld %r4, 984(%r3)
	or %r5, %r5, %r4
	ld %r4, 992(%r3)
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
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r4, 928(%r3)
	ld %r5, 832(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r10, 1120(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 856(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 864(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 872(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 928(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 936(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 944(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
