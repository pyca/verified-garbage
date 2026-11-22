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
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P192_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P192_FRAME_CONSTS}
	mtlr %r11
	li %r31, 51
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
	bl {vg_p192_validate}
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
	li %r0, 0
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
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
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P192_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P192_FRAME_CONSTS}
	mtlr %r11
	li %r31, 51
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
21:
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
	bne %cr0, 21b
	ld %r4, 184(%r3)
	std %r4, 760(%r3)
	ld %r4, 192(%r3)
	std %r4, 768(%r3)
	ld %r4, 200(%r3)
	std %r4, 776(%r3)
	li %r31, 192
22:
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
	bne %cr0, 22b
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
	li %r0, 0
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	blr
