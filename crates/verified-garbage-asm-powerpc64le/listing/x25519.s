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
