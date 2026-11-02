// The functions of `src/x25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	lwz %r7, 0(%r5)
	stw %r7, 0(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r5)
	stw %r7, 4(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r5)
	stw %r7, 8(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r5)
	stw %r7, 12(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r5)
	stw %r7, 16(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r5)
	stw %r7, 20(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r5)
	stw %r7, 24(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r5)
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 28(%r6)
	stw %r7, 124(%r6)
	li %r7, 1
	li %r8, 0
	lis %r5, 1
	ori %r5, %r5, 56129
	stw %r7, 32(%r6)
	stw %r8, 64(%r6)
	stw %r7, 128(%r6)
	stw %r5, 448(%r6)
	stw %r8, 36(%r6)
	stw %r8, 40(%r6)
	stw %r8, 44(%r6)
	stw %r8, 48(%r6)
	stw %r8, 52(%r6)
	stw %r8, 56(%r6)
	stw %r8, 60(%r6)
	stw %r8, 68(%r6)
	stw %r8, 72(%r6)
	stw %r8, 76(%r6)
	stw %r8, 80(%r6)
	stw %r8, 84(%r6)
	stw %r8, 88(%r6)
	stw %r8, 92(%r6)
	stw %r8, 132(%r6)
	stw %r8, 136(%r6)
	stw %r8, 140(%r6)
	stw %r8, 144(%r6)
	stw %r8, 148(%r6)
	stw %r8, 152(%r6)
	stw %r8, 156(%r6)
	stw %r8, 452(%r6)
	stw %r8, 456(%r6)
	stw %r8, 460(%r6)
	stw %r8, 464(%r6)
	stw %r8, 468(%r6)
	stw %r8, 472(%r6)
	stw %r8, 476(%r6)
	addi %r9, %r6, 0
	li %r11, 32
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 608(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 609(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 610(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 611(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 612(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 613(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 614(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 615(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r7, 0
	stb %r7, 608(%r6)
	stb %r7, 609(%r6)
	stb %r7, 610(%r6)
	li %r7, 1
	stb %r7, 862(%r6)
	li %r12, 255
	li %r0, 0
21:
	addi %r12, %r12, -1
	add %r4, %r6, %r12
	lbz %r4, 608(%r4)
	xor %r0, %r0, %r4
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 32(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 108(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 112(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 112(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 116(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 116(%r6)
	lwz %r5, 56(%r6)
	lwz %r7, 120(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 120(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 124(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 124(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 128(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 128(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 132(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 132(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 136(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 136(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 140(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 140(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 144(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 144(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 148(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 148(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 152(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 152(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 156(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 156(%r6)
	addi %r0, %r4, 0
	li %r10, 38
	li %r8, 0
	lwz %r7, 32(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
22:
	lwz %r4, 160(%r9)
	li %r8, 0
	lwz %r5, 160(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 164(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 32(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 192(%r6)
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 192(%r6)
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
23:
	lwz %r4, 192(%r9)
	li %r8, 0
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 336(%r6)
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 340(%r6)
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 344(%r6)
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 348(%r6)
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 288(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 320(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 324(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 328(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 332(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 336(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 340(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 344(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 348(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 96(%r6)
	lwz %r5, 128(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 132(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 136(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 140(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	lwz %r5, 144(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lwz %r5, 148(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lwz %r5, 152(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lwz %r5, 156(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 224(%r6)
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 224(%r6)
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 96(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 128(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 132(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 136(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 140(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 144(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 148(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 152(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 156(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 256(%r6)
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 256(%r6)
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
24:
	lwz %r4, 256(%r9)
	li %r8, 0
	lwz %r5, 160(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 164(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
25:
	lwz %r4, 224(%r9)
	li %r8, 0
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 384(%r6)
	lwz %r5, 416(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	lwz %r5, 420(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	lwz %r5, 424(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	lwz %r5, 428(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	lwz %r5, 432(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	lwz %r5, 436(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	lwz %r5, 440(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	lwz %r5, 444(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
26:
	lwz %r4, 96(%r9)
	li %r8, 0
	lwz %r5, 96(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 100(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 104(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 108(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 112(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 116(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 120(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 124(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 384(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 416(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 420(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 424(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 428(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 432(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 436(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 440(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 444(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
27:
	lwz %r4, 128(%r9)
	li %r8, 0
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
28:
	lwz %r4, 0(%r9)
	li %r8, 0
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
29:
	lwz %r4, 288(%r9)
	li %r8, 0
	lwz %r5, 320(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 324(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 328(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 332(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 336(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 340(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 344(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 348(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
210:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 352(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 356(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 360(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 364(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 368(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 372(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 376(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 380(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 210b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 288(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
211:
	lwz %r4, 352(%r9)
	li %r8, 0
	lwz %r5, 64(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 68(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 72(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 76(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 80(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 84(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 88(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 92(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 211b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 32(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 108(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 112(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 112(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 116(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 116(%r6)
	lwz %r5, 56(%r6)
	lwz %r7, 120(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 120(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 124(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 124(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 128(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 128(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 132(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 132(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 136(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 136(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 140(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 140(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 144(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 144(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 148(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 148(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 152(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 152(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 156(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 156(%r6)
	li %r4, 1
	li %r5, 0
	stw %r4, 480(%r6)
	stw %r5, 484(%r6)
	stw %r5, 488(%r6)
	stw %r5, 492(%r6)
	stw %r5, 496(%r6)
	stw %r5, 500(%r6)
	stw %r5, 504(%r6)
	stw %r5, 508(%r6)
	li %r12, 255
212:
	addi %r12, %r12, -1
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
213:
	lwz %r4, 480(%r9)
	li %r8, 0
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 504(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 508(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	addi %r5, %r12, -4
	cmpldi %cr0, %r5, 0
	beq %cr0, 214f
	addi %r5, %r12, -2
	cmpldi %cr0, %r5, 0
	beq %cr0, 216f
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
218:
	lwz %r4, 480(%r9)
	li %r8, 0
	lwz %r5, 64(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 68(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 72(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 76(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 80(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 84(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 88(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 92(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 218b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	b 217f
216:
217:
	b 215f
214:
215:
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	addi %r9, %r6, 0
	li %r11, 8
219:
	lwz %r4, 32(%r9)
	li %r8, 0
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 544(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 548(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 552(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 556(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 560(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 564(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 504(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 568(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 508(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 572(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 576(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	li %r8, 0
	lwz %r7, 544(%r6)
	lwz %r5, 576(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	lwz %r5, 580(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	lwz %r5, 584(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	lwz %r5, 588(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	lwz %r5, 592(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	lwz %r5, 596(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	lwz %r5, 600(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	lwz %r5, 604(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	lwz %r7, 60(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 60(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 540(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 512(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 36(%r6)
	lwz %r7, 516(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 40(%r6)
	lwz %r7, 520(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 44(%r6)
	lwz %r7, 524(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 48(%r6)
	lwz %r7, 528(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 52(%r6)
	lwz %r7, 532(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 56(%r6)
	lwz %r7, 536(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 540(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	blr

vg_x25519_base:
	std %r14, 1024(%r5)
	std %r15, 1032(%r5)
	std %r16, 1040(%r5)
	std %r17, 1048(%r5)
	std %r18, 1056(%r5)
	std %r19, 1064(%r5)
	std %r26, 1072(%r5)
	std %r27, 1080(%r5)
	std %r28, 1088(%r5)
	std %r29, 1096(%r5)
	std %r30, 1104(%r5)
	std %r31, 1112(%r5)
	addi %r6, %r5, 0
	addi %r27, %r3, 0
	mflr %r7
	std %r7, 1120(%r6)
	addi %r14, %r4, 0
	li %r7, 0
	stw %r7, 64(%r6)
	stw %r7, 68(%r6)
	stw %r7, 72(%r6)
	stw %r7, 76(%r6)
	stw %r7, 80(%r6)
	stw %r7, 84(%r6)
	stw %r7, 88(%r6)
	stw %r7, 92(%r6)
	stw %r7, 96(%r6)
	stw %r7, 100(%r6)
	stw %r7, 104(%r6)
	stw %r7, 108(%r6)
	stw %r7, 112(%r6)
	stw %r7, 116(%r6)
	stw %r7, 120(%r6)
	stw %r7, 124(%r6)
	stw %r7, 128(%r6)
	stw %r7, 132(%r6)
	stw %r7, 136(%r6)
	stw %r7, 140(%r6)
	stw %r7, 144(%r6)
	stw %r7, 148(%r6)
	stw %r7, 152(%r6)
	stw %r7, 156(%r6)
	stw %r7, 160(%r6)
	stw %r7, 164(%r6)
	stw %r7, 168(%r6)
	stw %r7, 172(%r6)
	stw %r7, 176(%r6)
	stw %r7, 180(%r6)
	stw %r7, 184(%r6)
	stw %r7, 188(%r6)
	stw %r7, 192(%r6)
	stw %r7, 196(%r6)
	stw %r7, 200(%r6)
	stw %r7, 204(%r6)
	stw %r7, 208(%r6)
	stw %r7, 212(%r6)
	stw %r7, 216(%r6)
	stw %r7, 220(%r6)
	stw %r7, 224(%r6)
	stw %r7, 228(%r6)
	stw %r7, 232(%r6)
	stw %r7, 236(%r6)
	stw %r7, 240(%r6)
	stw %r7, 244(%r6)
	stw %r7, 248(%r6)
	stw %r7, 252(%r6)
	stw %r7, 256(%r6)
	stw %r7, 260(%r6)
	stw %r7, 264(%r6)
	stw %r7, 268(%r6)
	stw %r7, 272(%r6)
	stw %r7, 276(%r6)
	stw %r7, 280(%r6)
	stw %r7, 284(%r6)
	stw %r7, 288(%r6)
	stw %r7, 292(%r6)
	stw %r7, 296(%r6)
	stw %r7, 300(%r6)
	stw %r7, 304(%r6)
	stw %r7, 308(%r6)
	stw %r7, 312(%r6)
	stw %r7, 316(%r6)
	stw %r7, 320(%r6)
	stw %r7, 324(%r6)
	stw %r7, 328(%r6)
	stw %r7, 332(%r6)
	stw %r7, 336(%r6)
	stw %r7, 340(%r6)
	stw %r7, 344(%r6)
	stw %r7, 348(%r6)
	stw %r7, 352(%r6)
	stw %r7, 356(%r6)
	stw %r7, 360(%r6)
	stw %r7, 364(%r6)
	stw %r7, 368(%r6)
	stw %r7, 372(%r6)
	stw %r7, 376(%r6)
	stw %r7, 380(%r6)
	stw %r7, 384(%r6)
	stw %r7, 388(%r6)
	stw %r7, 392(%r6)
	stw %r7, 396(%r6)
	stw %r7, 400(%r6)
	stw %r7, 404(%r6)
	stw %r7, 408(%r6)
	stw %r7, 412(%r6)
	stw %r7, 416(%r6)
	stw %r7, 420(%r6)
	stw %r7, 424(%r6)
	stw %r7, 428(%r6)
	stw %r7, 432(%r6)
	stw %r7, 436(%r6)
	stw %r7, 440(%r6)
	stw %r7, 444(%r6)
	stw %r7, 448(%r6)
	stw %r7, 452(%r6)
	stw %r7, 456(%r6)
	stw %r7, 460(%r6)
	stw %r7, 464(%r6)
	stw %r7, 468(%r6)
	stw %r7, 472(%r6)
	stw %r7, 476(%r6)
	stw %r7, 480(%r6)
	stw %r7, 484(%r6)
	stw %r7, 488(%r6)
	stw %r7, 492(%r6)
	stw %r7, 496(%r6)
	stw %r7, 500(%r6)
	stw %r7, 504(%r6)
	stw %r7, 508(%r6)
	stw %r7, 512(%r6)
	stw %r7, 516(%r6)
	stw %r7, 520(%r6)
	stw %r7, 524(%r6)
	stw %r7, 528(%r6)
	stw %r7, 532(%r6)
	stw %r7, 536(%r6)
	stw %r7, 540(%r6)
	stw %r7, 544(%r6)
	stw %r7, 548(%r6)
	stw %r7, 552(%r6)
	stw %r7, 556(%r6)
	stw %r7, 560(%r6)
	stw %r7, 564(%r6)
	stw %r7, 568(%r6)
	stw %r7, 572(%r6)
	stw %r7, 576(%r6)
	stw %r7, 580(%r6)
	stw %r7, 584(%r6)
	stw %r7, 588(%r6)
	stw %r7, 592(%r6)
	stw %r7, 596(%r6)
	stw %r7, 600(%r6)
	stw %r7, 604(%r6)
	stw %r7, 608(%r6)
	stw %r7, 612(%r6)
	stw %r7, 616(%r6)
	stw %r7, 620(%r6)
	stw %r7, 624(%r6)
	stw %r7, 628(%r6)
	stw %r7, 632(%r6)
	stw %r7, 636(%r6)
	stw %r7, 640(%r6)
	stw %r7, 644(%r6)
	stw %r7, 648(%r6)
	stw %r7, 652(%r6)
	stw %r7, 656(%r6)
	stw %r7, 660(%r6)
	stw %r7, 664(%r6)
	stw %r7, 668(%r6)
	stw %r7, 672(%r6)
	stw %r7, 676(%r6)
	stw %r7, 680(%r6)
	stw %r7, 684(%r6)
	stw %r7, 688(%r6)
	stw %r7, 692(%r6)
	stw %r7, 696(%r6)
	stw %r7, 700(%r6)
	stw %r7, 704(%r6)
	stw %r7, 708(%r6)
	stw %r7, 712(%r6)
	stw %r7, 716(%r6)
	stw %r7, 720(%r6)
	stw %r7, 724(%r6)
	stw %r7, 728(%r6)
	stw %r7, 732(%r6)
	stw %r7, 736(%r6)
	stw %r7, 740(%r6)
	stw %r7, 744(%r6)
	stw %r7, 748(%r6)
	stw %r7, 752(%r6)
	stw %r7, 756(%r6)
	stw %r7, 760(%r6)
	stw %r7, 764(%r6)
	li %r7, 15
	lbz %r8, 0(%r14)
	and %r9, %r8, %r7
	stb %r9, 1152(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1153(%r6)
	lbz %r8, 1(%r14)
	and %r9, %r8, %r7
	stb %r9, 1154(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1155(%r6)
	lbz %r8, 2(%r14)
	and %r9, %r8, %r7
	stb %r9, 1156(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1157(%r6)
	lbz %r8, 3(%r14)
	and %r9, %r8, %r7
	stb %r9, 1158(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1159(%r6)
	lbz %r8, 4(%r14)
	and %r9, %r8, %r7
	stb %r9, 1160(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1161(%r6)
	lbz %r8, 5(%r14)
	and %r9, %r8, %r7
	stb %r9, 1162(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1163(%r6)
	lbz %r8, 6(%r14)
	and %r9, %r8, %r7
	stb %r9, 1164(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1165(%r6)
	lbz %r8, 7(%r14)
	and %r9, %r8, %r7
	stb %r9, 1166(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1167(%r6)
	lbz %r8, 8(%r14)
	and %r9, %r8, %r7
	stb %r9, 1168(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1169(%r6)
	lbz %r8, 9(%r14)
	and %r9, %r8, %r7
	stb %r9, 1170(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1171(%r6)
	lbz %r8, 10(%r14)
	and %r9, %r8, %r7
	stb %r9, 1172(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1173(%r6)
	lbz %r8, 11(%r14)
	and %r9, %r8, %r7
	stb %r9, 1174(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1175(%r6)
	lbz %r8, 12(%r14)
	and %r9, %r8, %r7
	stb %r9, 1176(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1177(%r6)
	lbz %r8, 13(%r14)
	and %r9, %r8, %r7
	stb %r9, 1178(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1179(%r6)
	lbz %r8, 14(%r14)
	and %r9, %r8, %r7
	stb %r9, 1180(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1181(%r6)
	lbz %r8, 15(%r14)
	and %r9, %r8, %r7
	stb %r9, 1182(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1183(%r6)
	lbz %r8, 16(%r14)
	and %r9, %r8, %r7
	stb %r9, 1184(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1185(%r6)
	lbz %r8, 17(%r14)
	and %r9, %r8, %r7
	stb %r9, 1186(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1187(%r6)
	lbz %r8, 18(%r14)
	and %r9, %r8, %r7
	stb %r9, 1188(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1189(%r6)
	lbz %r8, 19(%r14)
	and %r9, %r8, %r7
	stb %r9, 1190(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1191(%r6)
	lbz %r8, 20(%r14)
	and %r9, %r8, %r7
	stb %r9, 1192(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1193(%r6)
	lbz %r8, 21(%r14)
	and %r9, %r8, %r7
	stb %r9, 1194(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1195(%r6)
	lbz %r8, 22(%r14)
	and %r9, %r8, %r7
	stb %r9, 1196(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1197(%r6)
	lbz %r8, 23(%r14)
	and %r9, %r8, %r7
	stb %r9, 1198(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1199(%r6)
	lbz %r8, 24(%r14)
	and %r9, %r8, %r7
	stb %r9, 1200(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1201(%r6)
	lbz %r8, 25(%r14)
	and %r9, %r8, %r7
	stb %r9, 1202(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1203(%r6)
	lbz %r8, 26(%r14)
	and %r9, %r8, %r7
	stb %r9, 1204(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1205(%r6)
	lbz %r8, 27(%r14)
	and %r9, %r8, %r7
	stb %r9, 1206(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1207(%r6)
	lbz %r8, 28(%r14)
	and %r9, %r8, %r7
	stb %r9, 1208(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1209(%r6)
	lbz %r8, 29(%r14)
	and %r9, %r8, %r7
	stb %r9, 1210(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1211(%r6)
	lbz %r8, 30(%r14)
	and %r9, %r8, %r7
	stb %r9, 1212(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1213(%r6)
	lbz %r8, 31(%r14)
	and %r9, %r8, %r7
	stb %r9, 1214(%r6)
	rldicl %r9, %r8, 60, 4
	stb %r9, 1215(%r6)
	lbz %r7, 1152(%r6)
	li %r8, 8
	and %r7, %r7, %r8
	stb %r7, 1152(%r6)
	lbz %r7, 1215(%r6)
	li %r8, 7
	and %r7, %r7, %r8
	ori %r7, %r7, 4
	stb %r7, 1215(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 736(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 740(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 744(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 748(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 752(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 756(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 760(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 764(%r6)
	lis %r7, 3704
	ori %r7, %r7, 19732
	stw %r7, 64(%r6)
	lis %r7, 9506
	ori %r7, %r7, 12927
	stw %r7, 68(%r6)
	lis %r7, -20265
	ori %r7, %r7, 5405
	stw %r7, 72(%r6)
	lis %r7, 3292
	ori %r7, %r7, 55882
	stw %r7, 76(%r6)
	lis %r7, -29415
	ori %r7, %r7, 56252
	stw %r7, 80(%r6)
	lis %r7, 24478
	ori %r7, %r7, 1244
	stw %r7, 84(%r6)
	lis %r7, 13402
	ori %r7, %r7, 6932
	stw %r7, 88(%r6)
	lis %r7, 2631
	ori %r7, %r7, 62822
	stw %r7, 92(%r6)
	lis %r7, 7152
	ori %r7, %r7, 63212
	stw %r7, 96(%r6)
	lis %r7, -23240
	ori %r7, %r7, 46503
	stw %r7, 100(%r6)
	lis %r7, 23337
	ori %r7, %r7, 22843
	stw %r7, 104(%r6)
	lis %r7, 5943
	ori %r7, %r7, 47280
	stw %r7, 108(%r6)
	lis %r7, -25815
	ori %r7, %r7, 51705
	stw %r7, 112(%r6)
	lis %r7, 12652
	ori %r7, %r7, 22935
	stw %r7, 116(%r6)
	lis %r7, 13703
	ori %r7, %r7, 638
	stw %r7, 120(%r6)
	lis %r7, 2371
	ori %r7, %r7, 18230
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, 17697
	ori %r7, %r7, 21093
	stw %r7, 160(%r6)
	lis %r7, -12976
	ori %r7, %r7, 18186
	stw %r7, 164(%r6)
	lis %r7, 3071
	ori %r7, %r7, 40439
	stw %r7, 168(%r6)
	lis %r7, -1596
	ori %r7, %r7, 8693
	stw %r7, 172(%r6)
	lis %r7, -7482
	ori %r7, %r7, 32329
	stw %r7, 176(%r6)
	lis %r7, 3634
	ori %r7, %r7, 33041
	stw %r7, 180(%r6)
	lis %r7, -11717
	ori %r7, %r7, 49440
	stw %r7, 184(%r6)
	lis %r7, 14477
	ori %r7, %r7, 38278
	stw %r7, 188(%r6)
	li %r15, 0
	bcl 20, 31, 2f
2:
	mflr %r16
	addis %r16, %r16, ({VG_ED25519_COMB}
	addi %r16, %r16, ({VG_ED25519_COMB}
20:
	add %r12, %r6, %r15
	lbz %r12, 1152(%r12)
	li %r0, 0
	addi %r12, %r12, -8
	rldicl %r11, %r12, 1, 63
	subf %r11, %r11, %r0
	std %r11, 56(%r6)
	xor %r12, %r12, %r11
	subf %r12, %r11, %r12
	li %r3, 1
	xor %r3, %r12, %r3
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r0
	li %r4, 2
	xor %r4, %r12, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	subf %r4, %r4, %r0
	li %r5, 3
	xor %r5, %r12, %r5
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	subf %r5, %r5, %r0
	li %r7, 4
	xor %r7, %r12, %r7
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	subf %r7, %r7, %r0
	li %r8, 5
	xor %r8, %r12, %r8
	addi %r8, %r8, -1
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r0
	li %r9, 6
	xor %r9, %r12, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	subf %r9, %r9, %r0
	li %r10, 7
	xor %r10, %r12, %r10
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	subf %r10, %r10, %r0
	li %r11, 8
	xor %r11, %r12, %r11
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	addi %r17, %r12, -1
	rldicl %r17, %r17, 1, 63
	addi %r12, %r17, 0
	ld %r0, 0(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 96(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 192(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 288(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 384(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 480(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 576(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 672(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 192(%r6)
	li %r12, 0
	ld %r0, 8(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 104(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 200(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 296(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 392(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 488(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 584(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 680(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 200(%r6)
	li %r12, 0
	ld %r0, 16(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 112(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 208(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 304(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 400(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 496(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 592(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 688(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 208(%r6)
	li %r12, 0
	ld %r0, 24(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 120(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 216(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 312(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 408(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 504(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 600(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 696(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 216(%r6)
	addi %r12, %r17, 0
	ld %r0, 32(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 128(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 224(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 320(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 416(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 512(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 608(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 704(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 224(%r6)
	li %r12, 0
	ld %r0, 40(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 136(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 232(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 328(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 424(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 520(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 616(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 712(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 232(%r6)
	li %r12, 0
	ld %r0, 48(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 144(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 240(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 336(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 432(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 528(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 624(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 720(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 240(%r6)
	li %r12, 0
	ld %r0, 56(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 152(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 248(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 344(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 440(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 536(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 632(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 728(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 248(%r6)
	li %r12, 0
	ld %r0, 64(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 160(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 256(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 352(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 448(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 544(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 640(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 736(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 256(%r6)
	li %r12, 0
	ld %r0, 72(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 168(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 264(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 360(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 456(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 552(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 648(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 744(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 264(%r6)
	li %r12, 0
	ld %r0, 80(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 176(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 272(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 368(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 464(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 560(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 656(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 752(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 272(%r6)
	li %r12, 0
	ld %r0, 88(%r16)
	and %r0, %r0, %r3
	or %r12, %r12, %r0
	ld %r0, 184(%r16)
	and %r0, %r0, %r4
	or %r12, %r12, %r0
	ld %r0, 280(%r16)
	and %r0, %r0, %r5
	or %r12, %r12, %r0
	ld %r0, 376(%r16)
	and %r0, %r0, %r7
	or %r12, %r12, %r0
	ld %r0, 472(%r16)
	and %r0, %r0, %r8
	or %r12, %r12, %r0
	ld %r0, 568(%r16)
	and %r0, %r0, %r9
	or %r12, %r12, %r0
	ld %r0, 664(%r16)
	and %r0, %r0, %r10
	or %r12, %r12, %r0
	ld %r0, 760(%r16)
	and %r0, %r0, %r11
	or %r12, %r12, %r0
	std %r12, 280(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 736(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 280(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 284(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	ld %r11, 56(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 224(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 228(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 228(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 232(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 236(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 236(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 240(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 244(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 244(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 248(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 252(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 252(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 288(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 288(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 292(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 292(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 296(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 296(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 300(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 300(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 304(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 304(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 308(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 308(%r6)
	lwz %r5, 280(%r6)
	lwz %r7, 312(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 280(%r6)
	stw %r7, 312(%r6)
	lwz %r5, 284(%r6)
	lwz %r7, 316(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 284(%r6)
	stw %r7, 316(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 96(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 336(%r6)
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 340(%r6)
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 344(%r6)
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 348(%r6)
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
21:
	lwz %r4, 320(%r9)
	li %r8, 0
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 336(%r6)
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 340(%r6)
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 344(%r6)
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 348(%r6)
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 96(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
22:
	lwz %r4, 352(%r9)
	li %r8, 0
	lwz %r5, 224(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 228(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 232(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 236(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 240(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 244(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 248(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 252(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
23:
	lwz %r4, 160(%r9)
	li %r8, 0
	lwz %r5, 256(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 260(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 264(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 268(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 272(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 276(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 128(%r6)
	lwz %r5, 128(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lwz %r5, 132(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lwz %r5, 136(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lwz %r5, 140(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lwz %r5, 144(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lwz %r5, 148(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lwz %r5, 152(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lwz %r5, 156(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 352(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 320(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 324(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 328(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 332(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 336(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 340(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 344(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 348(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 352(%r6)
	lwz %r5, 320(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	lwz %r5, 324(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	lwz %r5, 328(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	lwz %r5, 332(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	lwz %r5, 336(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	lwz %r5, 340(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	lwz %r5, 344(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	lwz %r5, 348(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 416(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 384(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 388(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 392(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 396(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 400(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 404(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 408(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 412(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 416(%r6)
	lwz %r5, 384(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	lwz %r5, 388(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	lwz %r5, 392(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	lwz %r5, 396(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	lwz %r5, 400(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	lwz %r5, 404(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	lwz %r5, 408(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	lwz %r5, 412(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
24:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 512(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 516(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 520(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 524(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 528(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 532(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 536(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 540(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
25:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 504(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 508(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
26:
	lwz %r4, 512(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
27:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 504(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 508(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	addi %r15, %r15, 1
	addi %r16, %r16, 768
	addi %r7, %r15, -64
	cmpldi %cr0, %r7, 0
	bne %cr0, 20b
	li %r10, 38
	li %r8, 0
	lwz %r7, 128(%r6)
	lwz %r5, 96(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lwz %r5, 100(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lwz %r5, 104(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lwz %r5, 108(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lwz %r5, 112(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lwz %r5, 116(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lwz %r5, 120(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lwz %r5, 124(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 128(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 96(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 100(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 104(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 108(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 112(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 116(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 120(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 124(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	addi %r3, %r6, 0
	bl {vg_gf25519_r32_pow250}
	addi %r6, %r3, 0
	li %r12, 5
28:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
29:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	addi %r3, %r6, 0
	li %r4, 544
	li %r5, 544
	li %r6, 512
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 96
	li %r5, 96
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	lwz %r7, 64(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 892(%r6)
	lwz %r7, 892(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 892(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 924(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 924(%r6)
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 864(%r6)
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 868(%r6)
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 872(%r6)
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 876(%r6)
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 880(%r6)
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 884(%r6)
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 888(%r6)
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	xor %r5, %r5, %r7
	and %r5, %r5, %r11
	xor %r7, %r7, %r5
	stw %r7, 892(%r6)
	ld %r7, 1120(%r6)
	mtlr %r7
	addi %r14, %r27, 0
	lwz %r7, 864(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 868(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 872(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 876(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 880(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 884(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 888(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 892(%r6)
	stw %r7, 28(%r14)
	ld %r14, 1024(%r6)
	ld %r15, 1032(%r6)
	ld %r16, 1040(%r6)
	ld %r17, 1048(%r6)
	ld %r18, 1056(%r6)
	ld %r19, 1064(%r6)
	ld %r26, 1072(%r6)
	ld %r27, 1080(%r6)
	ld %r28, 1088(%r6)
	ld %r29, 1096(%r6)
	ld %r30, 1104(%r6)
	ld %r31, 1112(%r6)
	blr
