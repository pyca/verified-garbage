// The functions of `src/ecdsa_p192.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_verify:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 808(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 816(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 824(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 832(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 840(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 848(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 856(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 864(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
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
	or %r12, %r5, %r5
	li %r31, 24
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 808(%r4)
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
	li %r31, 24
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 352(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4288(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4289(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4290(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4291(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4292(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4293(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4294(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4295(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r31, 24
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 376(%r4)
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
	bne %cr0, 22b
	addi %r6, %r12, 24
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 784(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 792(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 800(%r3)
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
	addi %r6, %r14, 1
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
	lbz %r4, 0(%r14)
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
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 808(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 812(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 816(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 820(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 824(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 828(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 808(%r3)
	ld %r4, 816(%r3)
	or %r5, %r5, %r4
	ld %r4, 824(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 784(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 788(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 792(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 796(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 800(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 804(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 784(%r3)
	ld %r4, 792(%r3)
	or %r5, %r5, %r4
	ld %r4, 800(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	li %r4, 952
	li %r5, 784
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	ld %r4, 328(%r3)
	std %r4, 760(%r3)
	ld %r4, 336(%r3)
	std %r4, 768(%r3)
	ld %r4, 344(%r3)
	std %r4, 776(%r3)
	li %r31, 192
23:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	li %r4, 784
	li %r5, 760
	li %r6, 952
	bl {vg_p192_mul_mod_n}
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
	bne %cr0, 23b
	li %r4, 1024
	li %r5, 832
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1000
	li %r5, 808
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1048
	li %r5, 1024
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	li %r4, 1072
	li %r5, 1000
	li %r6, 760
	bl {vg_p192_mul_mod_n}
	li %r4, 880
	li %r5, 1048
	li %r6, 160
	bl {vg_p192_mul_mod_n}
	li %r4, 904
	li %r5, 1072
	li %r6, 160
	bl {vg_p192_mul_mod_n}
	li %r31, 24
24:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 880(%r4)
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
	ld %r4, 256(%r3)
	std %r4, 3576(%r3)
	ld %r4, 264(%r3)
	std %r4, 3584(%r3)
	ld %r4, 272(%r3)
	std %r4, 3592(%r3)
	ld %r4, 280(%r3)
	std %r4, 3600(%r3)
	ld %r4, 288(%r3)
	std %r4, 3608(%r3)
	ld %r4, 296(%r3)
	std %r4, 3616(%r3)
	ld %r4, 184(%r3)
	std %r4, 3624(%r3)
	ld %r4, 192(%r3)
	std %r4, 3632(%r3)
	ld %r4, 200(%r3)
	std %r4, 3640(%r3)
	ld %r4, 208(%r3)
	std %r4, 3648(%r3)
	ld %r4, 216(%r3)
	std %r4, 3656(%r3)
	ld %r4, 224(%r3)
	std %r4, 3664(%r3)
	ld %r4, 232(%r3)
	std %r4, 3672(%r3)
	ld %r4, 240(%r3)
	std %r4, 3680(%r3)
	ld %r4, 248(%r3)
	std %r4, 3688(%r3)
	li %r31, 192
25:
	addi %r31, %r31, -1
	ld %r4, 400(%r3)
	std %r4, 3504(%r3)
	ld %r4, 408(%r3)
	std %r4, 3512(%r3)
	ld %r4, 416(%r3)
	std %r4, 3520(%r3)
	ld %r4, 424(%r3)
	std %r4, 3528(%r3)
	ld %r4, 432(%r3)
	std %r4, 3536(%r3)
	ld %r4, 440(%r3)
	std %r4, 3544(%r3)
	ld %r4, 448(%r3)
	std %r4, 3552(%r3)
	ld %r4, 456(%r3)
	std %r4, 3560(%r3)
	ld %r4, 464(%r3)
	std %r4, 3568(%r3)
	bl {vg_p192_point_double}
	ld %r4, 3432(%r3)
	std %r4, 3504(%r3)
	ld %r4, 3440(%r3)
	std %r4, 3512(%r3)
	ld %r4, 3448(%r3)
	std %r4, 3520(%r3)
	ld %r4, 3456(%r3)
	std %r4, 3528(%r3)
	ld %r4, 3464(%r3)
	std %r4, 3536(%r3)
	ld %r4, 3472(%r3)
	std %r4, 3544(%r3)
	ld %r4, 3480(%r3)
	std %r4, 3552(%r3)
	ld %r4, 3488(%r3)
	std %r4, 3560(%r3)
	ld %r4, 3496(%r3)
	std %r4, 3568(%r3)
	bl {vg_p192_point_add}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 3504(%r3)
	ld %r5, 3432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 400(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 3440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 408(%r3)
	ld %r4, 3520(%r3)
	ld %r5, 3448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 416(%r3)
	ld %r4, 3528(%r3)
	ld %r5, 3456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 424(%r3)
	ld %r4, 3536(%r3)
	ld %r5, 3464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 432(%r3)
	ld %r4, 3544(%r3)
	ld %r5, 3472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 440(%r3)
	ld %r4, 3552(%r3)
	ld %r5, 3480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 448(%r3)
	ld %r4, 3560(%r3)
	ld %r5, 3488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 456(%r3)
	ld %r4, 3568(%r3)
	ld %r5, 3496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 464(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	ld %r4, 400(%r3)
	std %r4, 1048(%r3)
	ld %r4, 408(%r3)
	std %r4, 1056(%r3)
	ld %r4, 416(%r3)
	std %r4, 1064(%r3)
	ld %r4, 424(%r3)
	std %r4, 1072(%r3)
	ld %r4, 432(%r3)
	std %r4, 1080(%r3)
	ld %r4, 440(%r3)
	std %r4, 1088(%r3)
	ld %r4, 448(%r3)
	std %r4, 952(%r3)
	ld %r4, 456(%r3)
	std %r4, 960(%r3)
	ld %r4, 464(%r3)
	std %r4, 968(%r3)
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
	li %r31, 24
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 904(%r4)
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
	ld %r4, 976(%r3)
	std %r4, 3576(%r3)
	ld %r4, 984(%r3)
	std %r4, 3584(%r3)
	ld %r4, 992(%r3)
	std %r4, 3592(%r3)
	ld %r4, 1096(%r3)
	std %r4, 3600(%r3)
	ld %r4, 1104(%r3)
	std %r4, 3608(%r3)
	ld %r4, 1112(%r3)
	std %r4, 3616(%r3)
	ld %r4, 184(%r3)
	std %r4, 3624(%r3)
	ld %r4, 192(%r3)
	std %r4, 3632(%r3)
	ld %r4, 200(%r3)
	std %r4, 3640(%r3)
	ld %r4, 208(%r3)
	std %r4, 3648(%r3)
	ld %r4, 216(%r3)
	std %r4, 3656(%r3)
	ld %r4, 224(%r3)
	std %r4, 3664(%r3)
	ld %r4, 232(%r3)
	std %r4, 3672(%r3)
	ld %r4, 240(%r3)
	std %r4, 3680(%r3)
	ld %r4, 248(%r3)
	std %r4, 3688(%r3)
	li %r31, 192
27:
	addi %r31, %r31, -1
	ld %r4, 400(%r3)
	std %r4, 3504(%r3)
	ld %r4, 408(%r3)
	std %r4, 3512(%r3)
	ld %r4, 416(%r3)
	std %r4, 3520(%r3)
	ld %r4, 424(%r3)
	std %r4, 3528(%r3)
	ld %r4, 432(%r3)
	std %r4, 3536(%r3)
	ld %r4, 440(%r3)
	std %r4, 3544(%r3)
	ld %r4, 448(%r3)
	std %r4, 3552(%r3)
	ld %r4, 456(%r3)
	std %r4, 3560(%r3)
	ld %r4, 464(%r3)
	std %r4, 3568(%r3)
	bl {vg_p192_point_double}
	ld %r4, 3432(%r3)
	std %r4, 3504(%r3)
	ld %r4, 3440(%r3)
	std %r4, 3512(%r3)
	ld %r4, 3448(%r3)
	std %r4, 3520(%r3)
	ld %r4, 3456(%r3)
	std %r4, 3528(%r3)
	ld %r4, 3464(%r3)
	std %r4, 3536(%r3)
	ld %r4, 3472(%r3)
	std %r4, 3544(%r3)
	ld %r4, 3480(%r3)
	std %r4, 3552(%r3)
	ld %r4, 3488(%r3)
	std %r4, 3560(%r3)
	ld %r4, 3496(%r3)
	std %r4, 3568(%r3)
	bl {vg_p192_point_add}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 3504(%r3)
	ld %r5, 3432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 400(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 3440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 408(%r3)
	ld %r4, 3520(%r3)
	ld %r5, 3448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 416(%r3)
	ld %r4, 3528(%r3)
	ld %r5, 3456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 424(%r3)
	ld %r4, 3536(%r3)
	ld %r5, 3464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 432(%r3)
	ld %r4, 3544(%r3)
	ld %r5, 3472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 440(%r3)
	ld %r4, 3552(%r3)
	ld %r5, 3480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 448(%r3)
	ld %r4, 3560(%r3)
	ld %r5, 3488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 456(%r3)
	ld %r4, 3568(%r3)
	ld %r5, 3496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 464(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 616
	li %r5, 1048
	li %r6, 400
	bl {vg_p192_mul_mod_p}
	li %r4, 640
	li %r5, 1072
	li %r6, 424
	bl {vg_p192_mul_mod_p}
	li %r4, 664
	li %r5, 952
	li %r6, 448
	bl {vg_p192_mul_mod_p}
	li %r4, 688
	li %r5, 1048
	li %r6, 1072
	bl {vg_p192_add_mod_p}
	li %r4, 712
	li %r5, 400
	li %r6, 424
	bl {vg_p192_add_mod_p}
	li %r4, 688
	li %r5, 688
	li %r6, 712
	bl {vg_p192_mul_mod_p}
	li %r4, 712
	li %r5, 616
	li %r6, 640
	bl {vg_p192_add_mod_p}
	li %r4, 688
	li %r5, 688
	li %r6, 712
	bl {vg_p192_sub_mod_p}
	li %r4, 712
	li %r5, 1048
	li %r6, 952
	bl {vg_p192_add_mod_p}
	li %r4, 736
	li %r5, 400
	li %r6, 448
	bl {vg_p192_add_mod_p}
	li %r4, 712
	li %r5, 712
	li %r6, 736
	bl {vg_p192_mul_mod_p}
	li %r4, 736
	li %r5, 616
	li %r6, 664
	bl {vg_p192_add_mod_p}
	li %r4, 712
	li %r5, 712
	li %r6, 736
	bl {vg_p192_sub_mod_p}
	li %r4, 736
	li %r5, 1072
	li %r6, 952
	bl {vg_p192_add_mod_p}
	li %r4, 472
	li %r5, 424
	li %r6, 448
	bl {vg_p192_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 472
	bl {vg_p192_mul_mod_p}
	li %r4, 472
	li %r5, 640
	li %r6, 664
	bl {vg_p192_add_mod_p}
	li %r4, 736
	li %r5, 736
	li %r6, 472
	bl {vg_p192_sub_mod_p}
	li %r4, 520
	li %r5, 208
	li %r6, 712
	bl {vg_p192_mul_mod_p}
	li %r4, 472
	li %r5, 232
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 520
	li %r5, 472
	li %r6, 520
	bl {vg_p192_add_mod_p}
	li %r4, 472
	li %r5, 640
	li %r6, 520
	bl {vg_p192_sub_mod_p}
	li %r4, 520
	li %r5, 640
	li %r6, 520
	bl {vg_p192_add_mod_p}
	li %r4, 496
	li %r5, 472
	li %r6, 520
	bl {vg_p192_mul_mod_p}
	li %r4, 640
	li %r5, 616
	li %r6, 616
	bl {vg_p192_add_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 616
	bl {vg_p192_add_mod_p}
	li %r4, 664
	li %r5, 208
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 712
	li %r5, 232
	li %r6, 712
	bl {vg_p192_mul_mod_p}
	li %r4, 640
	li %r5, 640
	li %r6, 664
	bl {vg_p192_add_mod_p}
	li %r4, 664
	li %r5, 616
	li %r6, 664
	bl {vg_p192_sub_mod_p}
	li %r4, 664
	li %r5, 208
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 712
	li %r5, 712
	li %r6, 664
	bl {vg_p192_add_mod_p}
	li %r4, 616
	li %r5, 640
	li %r6, 712
	bl {vg_p192_mul_mod_p}
	li %r4, 496
	li %r5, 496
	li %r6, 616
	bl {vg_p192_add_mod_p}
	li %r4, 616
	li %r5, 736
	li %r6, 712
	bl {vg_p192_mul_mod_p}
	li %r4, 472
	li %r5, 688
	li %r6, 472
	bl {vg_p192_mul_mod_p}
	li %r4, 472
	li %r5, 472
	li %r6, 616
	bl {vg_p192_sub_mod_p}
	li %r4, 616
	li %r5, 688
	li %r6, 640
	bl {vg_p192_mul_mod_p}
	li %r4, 520
	li %r5, 736
	li %r6, 520
	bl {vg_p192_mul_mod_p}
	li %r4, 520
	li %r5, 520
	li %r6, 616
	bl {vg_p192_add_mod_p}
	ld %r4, 472(%r3)
	std %r4, 400(%r3)
	ld %r4, 480(%r3)
	std %r4, 408(%r3)
	ld %r4, 488(%r3)
	std %r4, 416(%r3)
	ld %r4, 496(%r3)
	std %r4, 424(%r3)
	ld %r4, 504(%r3)
	std %r4, 432(%r3)
	ld %r4, 512(%r3)
	std %r4, 440(%r3)
	ld %r4, 520(%r3)
	std %r4, 448(%r3)
	ld %r4, 528(%r3)
	std %r4, 456(%r3)
	ld %r4, 536(%r3)
	std %r4, 464(%r3)
	ld %r4, 184(%r3)
	std %r4, 760(%r3)
	ld %r4, 192(%r3)
	std %r4, 768(%r3)
	ld %r4, 200(%r3)
	std %r4, 776(%r3)
	li %r31, 192
28:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 784
	li %r5, 760
	li %r6, 448
	bl {vg_p192_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4288(%r4)
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
	bne %cr0, 28b
	li %r4, 880
	li %r5, 400
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 904
	li %r5, 880
	li %r6, 160
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 904
	li %r6, 304
	bl {vg_p192_mul_mod_n}
	li %r4, 1024
	li %r5, 976
	li %r6, 1000
	bl {vg_p192_sub_mod_n}
	ld %r5, 448(%r3)
	ld %r4, 456(%r3)
	or %r5, %r5, %r4
	ld %r4, 464(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r5, 1024(%r3)
	ld %r4, 1032(%r3)
	or %r5, %r5, %r4
	ld %r4, 1040(%r3)
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
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ecdsa_p192_sign:
	or %r6, %r7, %r7
	ld %r9, 24(%r8)
	addi %r10, %r9, -0
	cmpldi %cr0, %r10, 0
	beq %cr0, 20f
	addi %r10, %r9, -1
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
	addi %r10, %r9, -2
	cmpldi %cr0, %r10, 0
	beq %cr0, 24f
	addi %r10, %r9, -3
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
	addi %r10, %r9, -4
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
	addi %r10, %r9, -5
	cmpldi %cr0, %r10, 0
	beq %cr0, 210f
	addi %r10, %r9, -6
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 209
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 1
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 209
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
214:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 215f
	li %r12, 0
	b 216f
215:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 33
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 161
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r12, 1
216:
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	b 213f
212:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2329(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 77
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 205
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 1
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2329(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 77
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 205
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
217:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 218f
	li %r12, 0
	b 219f
218:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 29
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 157
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r12, 1
219:
	cmpldi %cr0, %r12, 0
	bne %cr0, 217b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
213:
	b 211f
210:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2365(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 113
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 241
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 1
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2365(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 113
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 241
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
220:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 221f
	li %r12, 0
	b 222f
221:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 193
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	li %r12, 1
222:
	cmpldi %cr0, %r12, 0
	bne %cr0, 220b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
211:
	b 29f
28:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 0
	stb %r8, 2304(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2349(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 97
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 225
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 1
	stb %r8, 2304(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2349(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 97
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 225
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
223:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 224f
	li %r12, 0
	b 225f
224:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 0
	stb %r8, 2304(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 49
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 177
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	li %r12, 1
225:
	cmpldi %cr0, %r12, 0
	bne %cr0, 223b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
29:
	b 27f
26:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 145
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 1
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 145
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
226:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 227f
	li %r12, 0
	b 228f
227:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 33
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 97
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r12, 1
228:
	cmpldi %cr0, %r12, 0
	bne %cr0, 226b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
27:
	b 25f
24:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
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
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2329(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 77
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 141
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 1
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2329(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 77
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 141
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
229:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 230f
	li %r12, 0
	b 231f
230:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 29
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 93
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r12, 1
231:
	cmpldi %cr0, %r12, 0
	bne %cr0, 229b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
25:
	b 23f
22:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 260(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 264(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 268(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 276(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 0
	stb %r8, 2276(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2321(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 69
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 133
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 1
	stb %r8, 2276(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2321(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 69
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 133
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
232:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 428(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 436(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 233f
	li %r12, 0
	b 234f
233:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 0
	stb %r8, 2276(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 21
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 85
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	li %r12, 1
234:
	cmpldi %cr0, %r12, 0
	bne %cr0, 232b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
23:
	b 21f
20:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 264(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 268(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 276(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 0
	stb %r8, 2272(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2317(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 129
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 1
	stb %r8, 2272(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2297(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2301(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2317(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 129
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
235:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 428(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 236f
	li %r12, 0
	b 237f
236:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 0
	stb %r8, 2272(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 17
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 81
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	li %r12, 1
237:
	cmpldi %cr0, %r12, 0
	bne %cr0, 235b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
21:
	blr
