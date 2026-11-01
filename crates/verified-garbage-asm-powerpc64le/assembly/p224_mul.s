// The functions of `src/p224_mul.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul:
	std %r31, 1504(%r3)
	mflr %r0
	std %r0, 1512(%r3)
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
	ld %r4, 512(%r3)
	std %r4, 992(%r3)
	ld %r4, 520(%r3)
	std %r4, 1000(%r3)
	ld %r4, 528(%r3)
	std %r4, 1008(%r3)
	ld %r4, 536(%r3)
	std %r4, 1016(%r3)
	ld %r4, 544(%r3)
	std %r4, 1024(%r3)
	ld %r4, 552(%r3)
	std %r4, 1032(%r3)
	ld %r4, 560(%r3)
	std %r4, 1040(%r3)
	ld %r4, 568(%r3)
	std %r4, 1048(%r3)
	ld %r4, 160(%r3)
	std %r4, 512(%r3)
	ld %r4, 168(%r3)
	std %r4, 520(%r3)
	ld %r4, 176(%r3)
	std %r4, 528(%r3)
	ld %r4, 184(%r3)
	std %r4, 536(%r3)
	ld %r4, 224(%r3)
	std %r4, 544(%r3)
	ld %r4, 232(%r3)
	std %r4, 552(%r3)
	ld %r4, 240(%r3)
	std %r4, 560(%r3)
	ld %r4, 248(%r3)
	std %r4, 568(%r3)
	ld %r4, 160(%r3)
	std %r4, 576(%r3)
	ld %r4, 168(%r3)
	std %r4, 584(%r3)
	ld %r4, 176(%r3)
	std %r4, 592(%r3)
	ld %r4, 184(%r3)
	std %r4, 600(%r3)
	ld %r4, 992(%r3)
	std %r4, 3424(%r3)
	ld %r4, 1000(%r3)
	std %r4, 3432(%r3)
	ld %r4, 1008(%r3)
	std %r4, 3440(%r3)
	ld %r4, 1016(%r3)
	std %r4, 3448(%r3)
	ld %r4, 1024(%r3)
	std %r4, 3456(%r3)
	ld %r4, 1032(%r3)
	std %r4, 3464(%r3)
	ld %r4, 1040(%r3)
	std %r4, 3472(%r3)
	ld %r4, 1048(%r3)
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
	li %r31, 224
21:
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
	bl {vg_p224_point_double}
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
	bl {vg_p224_point_add}
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
	bne %cr0, 21b
	ld %r0, 1512(%r3)
	mtlr %r0
	ld %r31, 1504(%r3)
	blr
