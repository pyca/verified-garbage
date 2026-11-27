// The functions of `src/ec_p192.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_public_key:
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 808(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 816(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
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
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P192_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P192_FRAME_CONSTS}
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
	addi %r4, %r4, 24
	addi %r9, %r9, 24
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1120(%r3)
	li %r31, 24
21:
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
	bne %cr0, 21b
	li %r31, 24
22:
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
	bne %cr0, 22b
	li %r31, 24
23:
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
	bne %cr0, 23b
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
24:
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
	bne %cr0, 24b
	bl {vg_p192_inv_mod_p}
	li %r4, 880
	li %r5, 400
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 904
	li %r5, 880
	li %r6, 160
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 424
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 1096
	li %r5, 976
	li %r6, 160
	bl {vg_p192_mul_mod_p}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 832(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 836(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 840(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 844(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 848(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 852(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 832(%r3)
	ld %r4, 840(%r3)
	or %r5, %r5, %r4
	ld %r4, 848(%r3)
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
	ld %r10, 1120(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 904(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 912(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 920(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 1096(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 1104(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 1112(%r3)
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
