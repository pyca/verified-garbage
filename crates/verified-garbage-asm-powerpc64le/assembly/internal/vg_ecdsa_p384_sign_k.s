// The functions of `src/internal/vg_ecdsa_p384_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1592(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 1600(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1608(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1616(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1624(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1632(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1640(%r3)
	li %r9, 40
	ldbrx %r8, %r5, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1688(%r3)
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P384_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P384_FRAME_CONSTS}
	mtlr %r11
	li %r31, 102
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
	std %r4, 2176(%r3)
	li %r31, 48
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1552(%r4)
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
	li %r31, 48
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 640(%r4)
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
	li %r31, 48
23:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 688(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4864(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4865(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4866(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4867(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4868(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4869(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4870(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4871(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 448(%r3)
	std %r4, 3120(%r3)
	ld %r4, 456(%r3)
	std %r4, 3128(%r3)
	ld %r4, 464(%r3)
	std %r4, 3136(%r3)
	ld %r4, 472(%r3)
	std %r4, 3144(%r3)
	ld %r4, 480(%r3)
	std %r4, 3152(%r3)
	ld %r4, 488(%r3)
	std %r4, 3160(%r3)
	ld %r4, 496(%r3)
	std %r4, 3168(%r3)
	ld %r4, 504(%r3)
	std %r4, 3176(%r3)
	ld %r4, 512(%r3)
	std %r4, 3184(%r3)
	ld %r4, 520(%r3)
	std %r4, 3192(%r3)
	ld %r4, 528(%r3)
	std %r4, 3200(%r3)
	ld %r4, 536(%r3)
	std %r4, 3208(%r3)
	ld %r4, 304(%r3)
	std %r4, 3216(%r3)
	ld %r4, 312(%r3)
	std %r4, 3224(%r3)
	ld %r4, 320(%r3)
	std %r4, 3232(%r3)
	ld %r4, 328(%r3)
	std %r4, 3240(%r3)
	ld %r4, 336(%r3)
	std %r4, 3248(%r3)
	ld %r4, 344(%r3)
	std %r4, 3256(%r3)
	ld %r4, 352(%r3)
	std %r4, 3264(%r3)
	ld %r4, 360(%r3)
	std %r4, 3272(%r3)
	ld %r4, 368(%r3)
	std %r4, 3280(%r3)
	ld %r4, 376(%r3)
	std %r4, 3288(%r3)
	ld %r4, 384(%r3)
	std %r4, 3296(%r3)
	ld %r4, 392(%r3)
	std %r4, 3304(%r3)
	ld %r4, 400(%r3)
	std %r4, 3312(%r3)
	ld %r4, 408(%r3)
	std %r4, 3320(%r3)
	ld %r4, 416(%r3)
	std %r4, 3328(%r3)
	ld %r4, 424(%r3)
	std %r4, 3336(%r3)
	ld %r4, 432(%r3)
	std %r4, 3344(%r3)
	ld %r4, 440(%r3)
	std %r4, 3352(%r3)
	lis %r11, -4057
	ori %r11, %r11, 56916
	stw %r11, 736(%r3)
	lis %r11, -20506
	ori %r11, %r11, 38189
	stw %r11, 740(%r3)
	lis %r11, -31050
	ori %r11, %r11, 36017
	stw %r11, 744(%r3)
	lis %r11, 23629
	ori %r11, %r11, 2599
	stw %r11, 748(%r3)
	lis %r11, 25600
	ori %r11, %r11, 59425
	stw %r11, 752(%r3)
	lis %r11, 28055
	ori %r11, %r11, 28791
	stw %r11, 756(%r3)
	lis %r11, 19392
	ori %r11, %r11, 13696
	stw %r11, 760(%r3)
	lis %r11, 17052
	ori %r11, %r11, 36727
	stw %r11, 764(%r3)
	lis %r11, -26757
	ori %r11, %r11, 58585
	stw %r11, 768(%r3)
	lis %r11, -15063
	ori %r11, %r11, 38916
	stw %r11, 772(%r3)
	lis %r11, 20809
	ori %r11, %r11, 1254
	stw %r11, 776(%r3)
	lis %r11, -9510
	ori %r11, %r11, 11779
	stw %r11, 780(%r3)
	lis %r11, 27446
	ori %r11, %r11, 54200
	stw %r11, 784(%r3)
	lis %r11, 18386
	ori %r11, %r11, 60468
	stw %r11, 788(%r3)
	lis %r11, -29572
	ori %r11, %r11, 37009
	stw %r11, 792(%r3)
	lis %r11, 1363
	ori %r11, %r11, 22554
	stw %r11, 796(%r3)
	lis %r11, 26487
	ori %r11, %r11, 29119
	stw %r11, 800(%r3)
	lis %r11, -17370
	ori %r11, %r11, 28232
	stw %r11, 804(%r3)
	lis %r11, -32225
	ori %r11, %r11, 54743
	stw %r11, 808(%r3)
	lis %r11, 14303
	ori %r11, %r11, 25750
	stw %r11, 812(%r3)
	lis %r11, 22703
	ori %r11, %r11, 63707
	stw %r11, 816(%r3)
	lis %r11, 9915
	ori %r11, %r11, 60213
	stw %r11, 820(%r3)
	lis %r11, 19073
	ori %r11, %r11, 42498
	stw %r11, 824(%r3)
	lis %r11, -11215
	ori %r11, %r11, 39948
	stw %r11, 828(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 832(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 836(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 840(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 844(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 848(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 852(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 856(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 860(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 864(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 868(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 876(%r3)
	li %r31, 55
24:
	addi %r31, %r31, -1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -54
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
	addis %r8, %r8, ({VG_P384_COMB}
	addi %r8, %r8, ({VG_P384_COMB}
	li %r4, 6144
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
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
	lxvd2x 50, %r8, %r5
	addi %r8, %r8, 16
	vsel %v5, %v5, %v18, %v19
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	li %r4, 3120
	stxvd2x 32, %r3, %r4
	li %r4, 3136
	stxvd2x 33, %r3, %r4
	li %r4, 3152
	stxvd2x 34, %r3, %r4
	li %r4, 3168
	stxvd2x 35, %r3, %r4
	li %r4, 3184
	stxvd2x 36, %r3, %r4
	li %r4, 3200
	stxvd2x 37, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3216(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3220(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3228(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3260(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3168(%r3)
	ld %r5, 3216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3168(%r3)
	ld %r4, 3176(%r3)
	ld %r5, 3224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3176(%r3)
	ld %r4, 3184(%r3)
	ld %r5, 3232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3184(%r3)
	ld %r4, 3192(%r3)
	ld %r5, 3240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3192(%r3)
	ld %r4, 3200(%r3)
	ld %r5, 3248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3200(%r3)
	ld %r4, 3208(%r3)
	ld %r5, 3256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3208(%r3)
	ld %r4, 3216(%r3)
	ld %r5, 208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3216(%r3)
	ld %r4, 3224(%r3)
	ld %r5, 216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3224(%r3)
	ld %r4, 3232(%r3)
	ld %r5, 224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r4, 3240(%r3)
	ld %r5, 232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3240(%r3)
	ld %r4, 3248(%r3)
	ld %r5, 240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3248(%r3)
	ld %r4, 3256(%r3)
	ld %r5, 248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3256(%r3)
	li %r4, 1024
	li %r5, 208
	li %r6, 3168
	bl {vg_p384_sub_mod_p}
	addi %r6, %r31, -54
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
	ld %r4, 3168(%r3)
	ld %r5, 1024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3168(%r3)
	ld %r4, 3176(%r3)
	ld %r5, 1032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3176(%r3)
	ld %r4, 3184(%r3)
	ld %r5, 1040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3184(%r3)
	ld %r4, 3192(%r3)
	ld %r5, 1048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3192(%r3)
	ld %r4, 3200(%r3)
	ld %r5, 1056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3200(%r3)
	ld %r4, 3208(%r3)
	ld %r5, 1064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3208(%r3)
	ld %r4, 736(%r3)
	std %r4, 2976(%r3)
	ld %r4, 744(%r3)
	std %r4, 2984(%r3)
	ld %r4, 752(%r3)
	std %r4, 2992(%r3)
	ld %r4, 760(%r3)
	std %r4, 3000(%r3)
	ld %r4, 768(%r3)
	std %r4, 3008(%r3)
	ld %r4, 776(%r3)
	std %r4, 3016(%r3)
	ld %r4, 784(%r3)
	std %r4, 3024(%r3)
	ld %r4, 792(%r3)
	std %r4, 3032(%r3)
	ld %r4, 800(%r3)
	std %r4, 3040(%r3)
	ld %r4, 808(%r3)
	std %r4, 3048(%r3)
	ld %r4, 816(%r3)
	std %r4, 3056(%r3)
	ld %r4, 824(%r3)
	std %r4, 3064(%r3)
	ld %r4, 832(%r3)
	std %r4, 3072(%r3)
	ld %r4, 840(%r3)
	std %r4, 3080(%r3)
	ld %r4, 848(%r3)
	std %r4, 3088(%r3)
	ld %r4, 856(%r3)
	std %r4, 3096(%r3)
	ld %r4, 864(%r3)
	std %r4, 3104(%r3)
	ld %r4, 872(%r3)
	std %r4, 3112(%r3)
	bl {vg_p384_point_add}
	ld %r4, 2832(%r3)
	std %r4, 736(%r3)
	ld %r4, 2840(%r3)
	std %r4, 744(%r3)
	ld %r4, 2848(%r3)
	std %r4, 752(%r3)
	ld %r4, 2856(%r3)
	std %r4, 760(%r3)
	ld %r4, 2864(%r3)
	std %r4, 768(%r3)
	ld %r4, 2872(%r3)
	std %r4, 776(%r3)
	ld %r4, 2880(%r3)
	std %r4, 784(%r3)
	ld %r4, 2888(%r3)
	std %r4, 792(%r3)
	ld %r4, 2896(%r3)
	std %r4, 800(%r3)
	ld %r4, 2904(%r3)
	std %r4, 808(%r3)
	ld %r4, 2912(%r3)
	std %r4, 816(%r3)
	ld %r4, 2920(%r3)
	std %r4, 824(%r3)
	ld %r4, 2928(%r3)
	std %r4, 832(%r3)
	ld %r4, 2936(%r3)
	std %r4, 840(%r3)
	ld %r4, 2944(%r3)
	std %r4, 848(%r3)
	ld %r4, 2952(%r3)
	std %r4, 856(%r3)
	ld %r4, 2960(%r3)
	std %r4, 864(%r3)
	ld %r4, 2968(%r3)
	std %r4, 872(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	bl {vg_p384_inv_mod_p}
	li %r4, 1696
	li %r5, 736
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1744
	li %r5, 1696
	li %r6, 256
	bl {vg_p384_mul_mod_p}
	li %r4, 1792
	li %r5, 1744
	li %r6, 208
	bl {vg_p384_add_mod_n}
	li %r4, 1840
	li %r5, 1552
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1600(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1604(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1608(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1612(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1616(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1620(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1624(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1628(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1632(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1636(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1640(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1644(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1600(%r3)
	ld %r4, 1608(%r3)
	or %r5, %r5, %r4
	ld %r4, 1616(%r3)
	or %r5, %r5, %r4
	ld %r4, 1624(%r3)
	or %r5, %r5, %r4
	ld %r4, 1632(%r3)
	or %r5, %r5, %r4
	ld %r4, 1640(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1552(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1556(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1560(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1564(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1568(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1572(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1576(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1580(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1584(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1588(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1592(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1596(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1552(%r3)
	ld %r4, 1560(%r3)
	or %r5, %r5, %r4
	ld %r4, 1568(%r3)
	or %r5, %r5, %r4
	ld %r4, 1576(%r3)
	or %r5, %r5, %r4
	ld %r4, 1584(%r3)
	or %r5, %r5, %r4
	ld %r4, 1592(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r5, 1792(%r3)
	ld %r4, 1800(%r3)
	or %r5, %r5, %r4
	ld %r4, 1808(%r3)
	or %r5, %r5, %r4
	ld %r4, 1816(%r3)
	or %r5, %r5, %r4
	ld %r4, 1824(%r3)
	or %r5, %r5, %r4
	ld %r4, 1832(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	bl {vg_p384_inv_mod_n}
	li %r4, 1888
	li %r5, 1792
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r4, 1936
	li %r5, 1600
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r4, 1984
	li %r5, 1648
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r4, 2032
	li %r5, 1888
	li %r6, 1936
	bl {vg_p384_mul_mod_n}
	li %r4, 2032
	li %r5, 2032
	li %r6, 1984
	bl {vg_p384_add_mod_n}
	li %r4, 2080
	li %r5, 1456
	li %r6, 2032
	bl {vg_p384_mul_mod_n}
	li %r4, 2128
	li %r5, 2080
	li %r6, 256
	bl {vg_p384_mul_mod_n}
	ld %r5, 2128(%r3)
	ld %r4, 2136(%r3)
	or %r5, %r5, %r4
	ld %r4, 2144(%r3)
	or %r5, %r5, %r4
	ld %r4, 2152(%r3)
	or %r5, %r5, %r4
	ld %r4, 2160(%r3)
	or %r5, %r5, %r4
	ld %r4, 2168(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r10, 2176(%r3)
	ld %r4, 1792(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 1800(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1808(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1816(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1824(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1832(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 2128(%r3)
	and %r4, %r4, %r10
	li %r6, 88
	stdbrx %r4, %r14, %r6
	ld %r4, 2136(%r3)
	and %r4, %r4, %r10
	li %r6, 80
	stdbrx %r4, %r14, %r6
	ld %r4, 2144(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 2152(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	ld %r4, 2160(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 2168(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
