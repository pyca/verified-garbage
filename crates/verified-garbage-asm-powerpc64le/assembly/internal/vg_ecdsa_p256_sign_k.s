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
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r4
	addis %r4, %r4, ({VG_P256_FRAME_CONSTS}
	addi %r4, %r4, ({VG_P256_FRAME_CONSTS}
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
	ld %r11, 24(%r4)
	std %r11, 88(%r9)
	addi %r4, %r4, 32
	addi %r9, %r9, 32
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 1472(%r3)
	li %r31, 32
21:
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
	bne %cr0, 21b
	li %r31, 32
22:
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
	bne %cr0, 22b
	li %r31, 32
23:
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
	bne %cr0, 23b
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
	li %r31, 0
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	beq %cr0, 24f
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
	lbz %r7, 4102(%r4)
	b 25f
24:
	li %r9, 0
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
	li %r7, 0
25:
	li %r5, 0
	subf %r5, %r7, %r5
	li %r6, 128
	and %r6, %r6, %r5
	subf %r9, %r6, %r9
	xor %r9, %r9, %r5
	subf %r9, %r5, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_P256_COMB}
	addi %r8, %r8, ({VG_P256_COMB}
	li %r4, 4096
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	li %r7, 1
26:
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 26b
	li %r4, 3424
	stxvd2x 32, %r3, %r4
	li %r4, 3440
	stxvd2x 33, %r3, %r4
	li %r4, 3456
	stxvd2x 34, %r3, %r4
	li %r4, 3472
	stxvd2x 35, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3488(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3492(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3508(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 3512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3516(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3456(%r3)
	ld %r5, 3488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 3496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 3504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 3512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
	ld %r4, 3488(%r3)
	ld %r5, 160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3488(%r3)
	ld %r4, 3496(%r3)
	ld %r5, 168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3496(%r3)
	ld %r4, 3504(%r3)
	ld %r5, 176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3504(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3512(%r3)
	li %r4, 704
	li %r5, 160
	li %r6, 3456
	bl {vg_p256_sub_mod_p}
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	beq %cr0, 27f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	li %r10, 0
	subf %r10, %r4, %r10
	b 28f
27:
	li %r10, 0
28:
	ld %r4, 3456(%r3)
	ld %r5, 704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
	ld %r4, 3424(%r3)
	std %r4, 512(%r3)
	ld %r4, 3432(%r3)
	std %r4, 520(%r3)
	ld %r4, 3440(%r3)
	std %r4, 528(%r3)
	ld %r4, 3448(%r3)
	std %r4, 536(%r3)
	ld %r4, 3456(%r3)
	std %r4, 544(%r3)
	ld %r4, 3464(%r3)
	std %r4, 552(%r3)
	ld %r4, 3472(%r3)
	std %r4, 560(%r3)
	ld %r4, 3480(%r3)
	std %r4, 568(%r3)
	ld %r4, 3488(%r3)
	std %r4, 576(%r3)
	ld %r4, 3496(%r3)
	std %r4, 584(%r3)
	ld %r4, 3504(%r3)
	std %r4, 592(%r3)
	ld %r4, 3512(%r3)
	std %r4, 600(%r3)
29:
	addi %r31, %r31, 1
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	beq %cr0, 210f
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
	lbz %r7, 4102(%r4)
	b 211f
210:
	li %r9, 0
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
	li %r7, 0
211:
	lbz %r5, 4095(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	subf %r5, %r7, %r5
	li %r6, 128
	and %r6, %r6, %r5
	subf %r9, %r6, %r9
	xor %r9, %r9, %r5
	subf %r9, %r5, %r9
	bcl 20, 31, 2f
2:
	mflr %r8
	addis %r8, %r8, ({VG_P256_COMB}
	addi %r8, %r8, ({VG_P256_COMB}
	li %r4, 4096
	mulld %r4, %r4, %r31
	add %r8, %r8, %r4
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	li %r7, 1
212:
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
	addi %r7, %r7, 1
	addi %r6, %r7, -65
	cmpldi %cr0, %r6, 0
	bne %cr0, 212b
	li %r4, 3424
	stxvd2x 32, %r3, %r4
	li %r4, 3440
	stxvd2x 33, %r3, %r4
	li %r4, 3456
	stxvd2x 34, %r3, %r4
	li %r4, 3472
	stxvd2x 35, %r3, %r4
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3488(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3492(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3496(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3508(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 3512(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3516(%r3)
	li %r7, 0
	xor %r10, %r9, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 3456(%r3)
	ld %r5, 3488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 3496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 3504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 3512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
	ld %r4, 3488(%r3)
	ld %r5, 160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3488(%r3)
	ld %r4, 3496(%r3)
	ld %r5, 168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3496(%r3)
	ld %r4, 3504(%r3)
	ld %r5, 176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3504(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3512(%r3)
	li %r4, 704
	li %r5, 160
	li %r6, 3456
	bl {vg_p256_sub_mod_p}
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	lbz %r4, 4102(%r4)
	li %r10, 0
	subf %r10, %r4, %r10
	b 214f
213:
	li %r10, 0
214:
	ld %r4, 3456(%r3)
	ld %r5, 704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3456(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3464(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3472(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3480(%r3)
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
	bl {vg_p256_point_madd}
	ld %r4, 576(%r3)
	ld %r5, 584(%r3)
	or %r4, %r4, %r5
	ld %r5, 592(%r3)
	or %r4, %r4, %r5
	ld %r5, 600(%r3)
	or %r4, %r4, %r5
	li %r5, 0
	subfc %r5, %r4, %r5
	subfe %r10, %r10, %r10
	ld %r4, 3424(%r3)
	ld %r5, 3232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r4, 3432(%r3)
	ld %r5, 3240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3240(%r3)
	ld %r4, 3440(%r3)
	ld %r5, 3248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3248(%r3)
	ld %r4, 3448(%r3)
	ld %r5, 3256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3256(%r3)
	ld %r4, 3456(%r3)
	ld %r5, 3264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3264(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 3272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3272(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 3280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3280(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 3288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3288(%r3)
	ld %r4, 3488(%r3)
	ld %r5, 3296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3296(%r3)
	ld %r4, 3496(%r3)
	ld %r5, 3304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3304(%r3)
	ld %r4, 3504(%r3)
	ld %r5, 3312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3312(%r3)
	ld %r4, 3512(%r3)
	ld %r5, 3320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3320(%r3)
	li %r4, 7
	mulld %r4, %r4, %r31
	add %r4, %r3, %r4
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	beq %cr0, 215f
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
	lbz %r7, 4102(%r4)
	b 216f
215:
	li %r9, 0
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
	li %r7, 0
216:
	lbz %r5, 4095(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	subf %r5, %r7, %r5
	li %r6, 128
	and %r6, %r6, %r5
	subf %r9, %r6, %r9
	xor %r9, %r9, %r5
	subf %r9, %r5, %r9
	li %r5, 0
	subfc %r5, %r9, %r5
	subfe %r10, %r10, %r10
	ld %r4, 512(%r3)
	ld %r5, 3232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 512(%r3)
	ld %r4, 520(%r3)
	ld %r5, 3240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 520(%r3)
	ld %r4, 528(%r3)
	ld %r5, 3248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 528(%r3)
	ld %r4, 536(%r3)
	ld %r5, 3256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 536(%r3)
	ld %r4, 544(%r3)
	ld %r5, 3264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 552(%r3)
	ld %r5, 3272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 560(%r3)
	ld %r5, 3280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 568(%r3)
	ld %r5, 3288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	ld %r4, 576(%r3)
	ld %r5, 3296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 576(%r3)
	ld %r4, 584(%r3)
	ld %r5, 3304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 584(%r3)
	ld %r4, 592(%r3)
	ld %r5, 3312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 592(%r3)
	ld %r4, 600(%r3)
	ld %r5, 3320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 600(%r3)
	addi %r6, %r31, -36
	cmpldi %cr0, %r6, 0
	bne %cr0, 29b
	ld %r4, 576(%r3)
	ld %r5, 584(%r3)
	or %r4, %r4, %r5
	ld %r5, 592(%r3)
	or %r4, %r4, %r5
	ld %r5, 600(%r3)
	or %r4, %r4, %r5
	li %r5, 0
	subfc %r5, %r4, %r5
	subfe %r10, %r10, %r10
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3464(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3468(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3472(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3476(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 3480(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3484(%r3)
	ld %r4, 3456(%r3)
	ld %r5, 544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 544(%r3)
	ld %r4, 3464(%r3)
	ld %r5, 552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 552(%r3)
	ld %r4, 3472(%r3)
	ld %r5, 560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 560(%r3)
	ld %r4, 3480(%r3)
	ld %r5, 568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 568(%r3)
	li %r4, 512
	li %r5, 512
	li %r6, 576
	bl {vg_p256_mul_mod_p}
	li %r4, 704
	li %r5, 576
	li %r6, 576
	bl {vg_p256_mul_mod_p}
	li %r4, 576
	li %r5, 704
	li %r6, 576
	bl {vg_p256_mul_mod_p}
	li %r4, 544
	li %r5, 544
	li %r6, 160
	bl {vg_p256_add_mod_p}
	bl {vg_p256_inv_mod_p}
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
	bl {vg_p256_inv_mod_n}
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
