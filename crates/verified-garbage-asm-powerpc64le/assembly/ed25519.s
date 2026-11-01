// The functions of `src/ed25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	std %r14, 1024(%r7)
	std %r15, 1032(%r7)
	std %r16, 1040(%r7)
	std %r17, 1048(%r7)
	std %r18, 1056(%r7)
	std %r19, 1064(%r7)
	std %r26, 1072(%r7)
	std %r27, 1080(%r7)
	std %r28, 1088(%r7)
	std %r29, 1096(%r7)
	std %r30, 1104(%r7)
	std %r31, 1112(%r7)
	addi %r18, %r3, 0
	addi %r17, %r6, 0
	addi %r6, %r7, 0
	addi %r14, %r4, 0
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	addi %r14, %r5, 0
	lwz %r7, 0(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 124(%r6)
	addi %r14, %r17, 0
	lwz %r7, 0(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 156(%r6)
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
20:
	lwz %r4, 96(%r9)
	li %r8, 0
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
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
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 896(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 900(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 904(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 908(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 912(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 916(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 920(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 924(%r6)
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r14, %r6, 512
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
	lwz %r7, 896(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 900(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 904(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 908(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 912(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 916(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 920(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 924(%r6)
	stw %r7, 60(%r14)
	li %r7, 0
	stw %r7, 160(%r6)
	stw %r7, 164(%r6)
	stw %r7, 168(%r6)
	stw %r7, 172(%r6)
	stw %r7, 176(%r6)
	stw %r7, 180(%r6)
	stw %r7, 184(%r6)
	stw %r7, 188(%r6)
	li %r15, 64
21:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 21b
	addi %r14, %r18, 0
	lwz %r7, 160(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 188(%r6)
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

vg_ed25519_public_key:
	stdu %r1, -176(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r20, 96(%r6)
	std %r21, 104(%r6)
	std %r22, 112(%r6)
	std %r23, 120(%r6)
	std %r0, 128(%r6)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r5, 0
	addi %r23, %r6, 0
	addi %r3, %r22, 0
	bl {vg_sha512_init}
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r21, 0
	li %r6, 32
	addi %r7, %r22, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r22, 0
	li %r4, 32
	addi %r5, %r23, 0
	addi %r6, %r22, 192
	bl {vg_sha512_finalize_scratch}
	ld %r8, 0(%r23)
	rldicl %r8, %r8, 61, 3
	rldicr %r8, %r8, 3, 60
	std %r8, 64(%r23)
	ld %r8, 8(%r23)
	std %r8, 72(%r23)
	ld %r8, 16(%r23)
	std %r8, 80(%r23)
	ld %r8, 24(%r23)
	rldicr %r8, %r8, 2, 61
	rldicl %r8, %r8, 62, 2
	lis %r9, 16384
	rldicr %r9, %r9, 32, 31
	or %r8, %r8, %r9
	std %r8, 88(%r23)
	addi %r3, %r20, 0
	addi %r4, %r23, 64
	addi %r5, %r22, 0
	bl {vg_ed25519_scalar_base}
	ld %r0, 128(%r23)
	ld %r20, 96(%r23)
	ld %r21, 104(%r23)
	ld %r22, 112(%r23)
	ld %r23, 120(%r23)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	addi %r1, %r1, 176
	blr

vg_ed25519_scalar_reduce:
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
	addi %r14, %r4, 0
	li %r7, 0
	stw %r7, 160(%r6)
	stw %r7, 164(%r6)
	stw %r7, 168(%r6)
	stw %r7, 172(%r6)
	stw %r7, 176(%r6)
	stw %r7, 180(%r6)
	stw %r7, 184(%r6)
	stw %r7, 188(%r6)
	li %r15, 64
20:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 160(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 220(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 20b
	addi %r14, %r27, 0
	lwz %r7, 160(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 188(%r6)
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

vg_ed25519_scalar_base:
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
	lis %r7, -28891
	ori %r7, %r7, 54554
	stw %r7, 64(%r6)
	lis %r7, -13994
	ori %r7, %r7, 11616
	stw %r7, 68(%r6)
	lis %r7, -27355
	ori %r7, %r7, 42930
	stw %r7, 72(%r6)
	lis %r7, 26924
	ori %r7, %r7, 51040
	stw %r7, 76(%r6)
	lis %r7, -554
	ori %r7, %r7, 56412
	stw %r7, 80(%r6)
	lis %r7, -16220
	ori %r7, %r7, 57905
	stw %r7, 84(%r6)
	lis %r7, -12946
	ori %r7, %r7, 21502
	stw %r7, 88(%r6)
	lis %r7, 8553
	ori %r7, %r7, 14035
	stw %r7, 92(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26200
	stw %r7, 96(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 100(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 104(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 108(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 112(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 116(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 120(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
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
	lis %r7, -23113
	ori %r7, %r7, 56739
	stw %r7, 160(%r6)
	lis %r7, 28126
	ori %r7, %r7, 35507
	stw %r7, 164(%r6)
	lis %r7, 30545
	ori %r7, %r7, 21237
	stw %r7, 168(%r6)
	lis %r7, 8432
	ori %r7, %r7, 40832
	stw %r7, 172(%r6)
	lis %r7, 25771
	ori %r7, %r7, 58237
	stw %r7, 176(%r6)
	lis %r7, 26346
	ori %r7, %r7, 20110
	stw %r7, 180(%r6)
	lis %r7, -10357
	ori %r7, %r7, 30309
	stw %r7, 184(%r6)
	lis %r7, 26503
	ori %r7, %r7, 24335
	stw %r7, 188(%r6)
	addi %r19, %r14, 0
	lis %r7, 4953
	ori %r7, %r7, 30883
	stw %r7, 576(%r6)
	lis %r7, 30187
	ori %r7, %r7, 19914
	stw %r7, 580(%r6)
	lis %r7, 16705
	ori %r7, %r7, 55467
	stw %r7, 584(%r6)
	lis %r7, 112
	ori %r7, %r7, 2637
	stw %r7, 588(%r6)
	lis %r7, 30585
	ori %r7, %r7, 59544
	stw %r7, 592(%r6)
	lis %r7, -29497
	ori %r7, %r7, 16505
	stw %r7, 596(%r6)
	lis %r7, 11119
	ori %r7, %r7, 65139
	stw %r7, 600(%r6)
	lis %r7, 20995
	ori %r7, %r7, 27886
	stw %r7, 604(%r6)
	li %r16, 0
20:
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	li %r15, 16
21:
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r15, %r15, -1
	cmpldi %cr0, %r15, 0
	bne %cr0, 21b
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 20b
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
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
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 168(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 172(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 176(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 180(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 184(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 188(%r6)
	li %r26, 16
22:
	addi %r26, %r26, -1
	addi %r16, %r26, 0
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	li %r16, 0
23:
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 23b
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	rldicr %r7, %r26, 1, 62
	add %r14, %r19, %r7
	lbz %r7, 0(%r14)
	lbz %r8, 1(%r14)
	rldicr %r8, %r8, 8, 55
	add %r7, %r7, %r8
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 32(%r6)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 33(%r6)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 34(%r6)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 35(%r6)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 36(%r6)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 37(%r6)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 38(%r6)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 39(%r6)
	rldicr %r8, %r7, 55, 8
	rldicl %r8, %r8, 1, 63
	stb %r8, 40(%r6)
	rldicr %r8, %r7, 54, 9
	rldicl %r8, %r8, 1, 63
	stb %r8, 41(%r6)
	rldicr %r8, %r7, 53, 10
	rldicl %r8, %r8, 1, 63
	stb %r8, 42(%r6)
	rldicr %r8, %r7, 52, 11
	rldicl %r8, %r8, 1, 63
	stb %r8, 43(%r6)
	rldicr %r8, %r7, 51, 12
	rldicl %r8, %r8, 1, 63
	stb %r8, 44(%r6)
	rldicr %r8, %r7, 50, 13
	rldicl %r8, %r8, 1, 63
	stb %r8, 45(%r6)
	rldicr %r8, %r7, 49, 14
	rldicl %r8, %r8, 1, 63
	stb %r8, 46(%r6)
	rldicr %r8, %r7, 48, 15
	rldicl %r8, %r8, 1, 63
	stb %r8, 47(%r6)
	li %r16, 16
24:
	addi %r16, %r16, -1
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	add %r7, %r6, %r16
	lbz %r7, 32(%r7)
	addi %r11, %r7, -1
	lwz %r5, 64(%r6)
	lwz %r7, 608(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 612(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 616(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 620(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 624(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 628(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 632(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 636(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 640(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 644(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 648(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 652(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 656(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 660(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 664(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 668(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 672(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 676(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 680(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 684(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 688(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 692(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 696(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 700(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 704(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 708(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 712(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 716(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 720(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 724(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 728(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 732(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 732(%r6)
	cmpldi %cr0, %r16, 0
	bne %cr0, 24b
	cmpldi %cr0, %r26, 0
	bne %cr0, 22b
	addi %r3, %r6, 0
	bl {vg_gf25519_r32_pow250}
	addi %r6, %r3, 0
	li %r12, 5
25:
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
	bne %cr0, 26b
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
	bne %cr0, 25b
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
	lwz %r7, 864(%r6)
	rldicr %r17, %r7, 63, 0
	rldicl %r17, %r17, 32, 32
	lwz %r7, 96(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 124(%r6)
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
	lwz %r7, 892(%r6)
	add %r7, %r7, %r17
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

vg_ed25519_sign_cached:
	stdu %r1, -320(%r1)
	addi %r9, %r1, 32
	mflr %r0
	std %r20, 224(%r9)
	std %r21, 232(%r9)
	std %r22, 240(%r9)
	std %r23, 248(%r9)
	std %r24, 256(%r9)
	std %r25, 264(%r9)
	std %r0, 272(%r9)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r6, 0
	addi %r23, %r7, 0
	addi %r24, %r8, 0
	addi %r25, %r9, 0
	ld %r8, 0(%r5)
	std %r8, 192(%r25)
	ld %r8, 8(%r5)
	std %r8, 200(%r25)
	ld %r8, 16(%r5)
	std %r8, 208(%r25)
	ld %r8, 24(%r5)
	std %r8, 216(%r25)
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r21, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	ld %r8, 128(%r25)
	rldicl %r8, %r8, 61, 3
	rldicr %r8, %r8, 3, 60
	std %r8, 0(%r25)
	ld %r8, 136(%r25)
	std %r8, 8(%r25)
	ld %r8, 144(%r25)
	std %r8, 16(%r25)
	ld %r8, 152(%r25)
	rldicr %r8, %r8, 2, 61
	rldicl %r8, %r8, 62, 2
	lis %r9, 16384
	rldicr %r9, %r9, 32, 31
	or %r8, %r8, %r9
	std %r8, 24(%r25)
	ld %r8, 160(%r25)
	std %r8, 32(%r25)
	ld %r8, 168(%r25)
	std %r8, 40(%r25)
	ld %r8, 176(%r25)
	std %r8, 48(%r25)
	ld %r8, 184(%r25)
	std %r8, 56(%r25)
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r25, 32
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r22, 0
	addi %r6, %r23, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r23, 32
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 64
	addi %r4, %r25, 128
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	addi %r3, %r20, 0
	addi %r4, %r25, 64
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_base}
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r20, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r25, 192
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 64
	addi %r5, %r22, 0
	addi %r6, %r23, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r23, 64
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 96
	addi %r4, %r25, 128
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	addi %r3, %r20, 32
	addi %r4, %r25, 64
	addi %r5, %r25, 96
	addi %r6, %r25, 0
	addi %r7, %r24, 0
	bl {vg_ed25519_scalar_mul_add}
	ld %r0, 272(%r25)
	ld %r20, 224(%r25)
	ld %r21, 232(%r25)
	ld %r22, 240(%r25)
	ld %r23, 248(%r25)
	ld %r24, 256(%r25)
	ld %r25, 264(%r25)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	addi %r1, %r1, 320
	blr

vg_ed25519_verify_equation:
	std %r14, 1024(%r6)
	std %r15, 1032(%r6)
	std %r16, 1040(%r6)
	std %r17, 1048(%r6)
	std %r18, 1056(%r6)
	std %r19, 1064(%r6)
	std %r26, 1072(%r6)
	std %r27, 1080(%r6)
	std %r28, 1088(%r6)
	std %r29, 1096(%r6)
	std %r30, 1104(%r6)
	std %r31, 1112(%r6)
	addi %r29, %r3, 0
	addi %r30, %r4, 0
	addi %r31, %r5, 0
	mflr %r7
	std %r7, 1120(%r6)
	addi %r14, %r30, 32
	lwz %r7, 0(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 188(%r6)
	li %r8, 1
	lwz %r7, 160(%r6)
	lis %r5, -23798
	ori %r5, %r5, 11282
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -22547
	ori %r5, %r5, 40165
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	lis %r5, 23816
	ori %r5, %r5, 25385
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -5343
	ori %r5, %r5, 1569
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, -1
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, -4097
	ori %r5, %r5, 65535
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
	li %r17, 0
	b 21f
20:
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
	addi %r27, %r29, 0
	li %r28, 7776
	li %r18, 1
22:
	addi %r14, %r27, 0
	lwz %r7, 0(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 124(%r6)
	rldicl %r8, %r7, 33, 31
	std %r8, 24(%r6)
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 124(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 124(%r6)
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
	li %r5, 0
	lwz %r7, 96(%r6)
	lwz %r8, 864(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 100(%r6)
	lwz %r8, 868(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 104(%r6)
	lwz %r8, 872(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 108(%r6)
	lwz %r8, 876(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 112(%r6)
	lwz %r8, 880(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 116(%r6)
	lwz %r8, 884(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 120(%r6)
	lwz %r8, 888(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	lwz %r7, 124(%r6)
	lwz %r8, 892(%r6)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 23f
	li %r17, 0
	b 24f
23:
	lis %r7, 4953
	ori %r7, %r7, 30883
	stw %r7, 576(%r6)
	lis %r7, 30187
	ori %r7, %r7, 19914
	stw %r7, 580(%r6)
	lis %r7, 16705
	ori %r7, %r7, 55467
	stw %r7, 584(%r6)
	lis %r7, 112
	ori %r7, %r7, 2637
	stw %r7, 588(%r6)
	lis %r7, 30585
	ori %r7, %r7, 59544
	stw %r7, 592(%r6)
	lis %r7, -29497
	ori %r7, %r7, 16505
	stw %r7, 596(%r6)
	lis %r7, 11119
	ori %r7, %r7, 65139
	stw %r7, 600(%r6)
	lis %r7, 20995
	ori %r7, %r7, 27886
	stw %r7, 604(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 192(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 196(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 200(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 204(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 208(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 212(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 216(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 220(%r6)
	addi %r3, %r6, 0
	li %r4, 224
	li %r5, 96
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 192(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 196(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 200(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 204(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 208(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 212(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 216(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 220(%r6)
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
	addi %r3, %r6, 0
	li %r4, 288
	li %r5, 576
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 288
	li %r5, 288
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	lwz %r7, 288(%r6)
	lwz %r5, 192(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	lwz %r5, 196(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	lwz %r5, 200(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	lwz %r5, 204(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	lwz %r5, 208(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	lwz %r5, 212(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	lwz %r5, 216(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	lwz %r5, 220(%r6)
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
	addi %r3, %r6, 0
	li %r4, 320
	li %r5, 288
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 352
	li %r5, 320
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 352
	li %r6, 352
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 384
	li %r6, 288
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 128
	li %r5, 256
	li %r6, 384
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	bl {vg_gf25519_r32_pow250}
	addi %r6, %r3, 0
	li %r12, 2
25:
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
	bne %cr0, 26b
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
	bne %cr0, 25b
	addi %r3, %r6, 0
	li %r4, 544
	li %r5, 544
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 280(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 284(%r6)
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
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 256
	li %r6, 352
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 544
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 288
	li %r6, 64
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 416
	li %r6, 64
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 416(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 280(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 284(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 27f
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 416(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 448(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 452(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 456(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 460(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 464(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 468(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 472(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 476(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 29f
	li %r17, 0
	b 210f
29:
	lis %r7, 18958
	ori %r7, %r7, 41136
	stw %r7, 640(%r6)
	lis %r7, -15122
	ori %r7, %r7, 6951
	stw %r7, 644(%r6)
	lis %r7, -21201
	ori %r7, %r7, 58488
	stw %r7, 648(%r6)
	lis %r7, 12099
	ori %r7, %r7, 6150
	stw %r7, 652(%r6)
	lis %r7, 15867
	ori %r7, %r7, 55207
	stw %r7, 656(%r6)
	lis %r7, 11085
	ori %r7, %r7, 153
	stw %r7, 660(%r6)
	lis %r7, 20417
	ori %r7, %r7, 57099
	stw %r7, 664(%r6)
	lis %r7, 11139
	ori %r7, %r7, 9344
	stw %r7, 668(%r6)
	addi %r3, %r6, 0
	li %r4, 64
	li %r5, 64
	li %r6, 640
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 211f
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
	lwz %r7, 864(%r6)
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 213f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
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
	b 214f
213:
214:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 212f
211:
	ld %r5, 24(%r6)
	cmpldi %cr0, %r5, 0
	bne %cr0, 215f
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
	lwz %r7, 864(%r6)
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 217f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
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
	b 218f
217:
218:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 216f
215:
	li %r17, 0
216:
212:
210:
	b 28f
27:
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 219f
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
	lwz %r7, 864(%r6)
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 221f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
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
	b 222f
221:
222:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 220f
219:
	ld %r5, 24(%r6)
	cmpldi %cr0, %r5, 0
	bne %cr0, 223f
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
	lwz %r7, 864(%r6)
	rldicr %r7, %r7, 63, 0
	rldicl %r7, %r7, 1, 63
	ld %r8, 24(%r6)
	xor %r5, %r7, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 225f
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
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
	b 226f
225:
226:
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
	addi %r3, %r6, 0
	li %r4, 160
	li %r5, 64
	li %r6, 96
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r17, 1
	b 224f
223:
	li %r17, 0
224:
220:
28:
24:
	and %r18, %r18, %r17
	add %r14, %r6, %r28
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	addi %r27, %r30, 0
	addi %r28, %r28, 128
	addi %r7, %r28, -8032
	cmpldi %cr0, %r7, 0
	bne %cr0, 22b
	cmpldi %cr0, %r18, 0
	bne %cr0, 227f
	li %r17, 0
	b 228f
227:
	addi %r14, %r30, 32
	lis %r7, -28891
	ori %r7, %r7, 54554
	stw %r7, 64(%r6)
	lis %r7, -13994
	ori %r7, %r7, 11616
	stw %r7, 68(%r6)
	lis %r7, -27355
	ori %r7, %r7, 42930
	stw %r7, 72(%r6)
	lis %r7, 26924
	ori %r7, %r7, 51040
	stw %r7, 76(%r6)
	lis %r7, -554
	ori %r7, %r7, 56412
	stw %r7, 80(%r6)
	lis %r7, -16220
	ori %r7, %r7, 57905
	stw %r7, 84(%r6)
	lis %r7, -12946
	ori %r7, %r7, 21502
	stw %r7, 88(%r6)
	lis %r7, 8553
	ori %r7, %r7, 14035
	stw %r7, 92(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26200
	stw %r7, 96(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 100(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 104(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 108(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 112(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 116(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
	stw %r7, 120(%r6)
	lis %r7, 26214
	ori %r7, %r7, 26214
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
	lis %r7, -23113
	ori %r7, %r7, 56739
	stw %r7, 160(%r6)
	lis %r7, 28126
	ori %r7, %r7, 35507
	stw %r7, 164(%r6)
	lis %r7, 30545
	ori %r7, %r7, 21237
	stw %r7, 168(%r6)
	lis %r7, 8432
	ori %r7, %r7, 40832
	stw %r7, 172(%r6)
	lis %r7, 25771
	ori %r7, %r7, 58237
	stw %r7, 176(%r6)
	lis %r7, 26346
	ori %r7, %r7, 20110
	stw %r7, 180(%r6)
	lis %r7, -10357
	ori %r7, %r7, 30309
	stw %r7, 184(%r6)
	lis %r7, 26503
	ori %r7, %r7, 24335
	stw %r7, 188(%r6)
	addi %r19, %r14, 0
	lis %r7, 4953
	ori %r7, %r7, 30883
	stw %r7, 576(%r6)
	lis %r7, 30187
	ori %r7, %r7, 19914
	stw %r7, 580(%r6)
	lis %r7, 16705
	ori %r7, %r7, 55467
	stw %r7, 584(%r6)
	lis %r7, 112
	ori %r7, %r7, 2637
	stw %r7, 588(%r6)
	lis %r7, 30585
	ori %r7, %r7, 59544
	stw %r7, 592(%r6)
	lis %r7, -29497
	ori %r7, %r7, 16505
	stw %r7, 596(%r6)
	lis %r7, 11119
	ori %r7, %r7, 65139
	stw %r7, 600(%r6)
	lis %r7, 20995
	ori %r7, %r7, 27886
	stw %r7, 604(%r6)
	li %r16, 0
229:
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	li %r15, 16
230:
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r15, %r15, -1
	cmpldi %cr0, %r15, 0
	bne %cr0, 230b
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 229b
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
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
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 168(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 172(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 176(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 180(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 184(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 188(%r6)
	li %r26, 16
231:
	addi %r26, %r26, -1
	addi %r16, %r26, 0
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	li %r16, 0
232:
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 232b
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	rldicr %r7, %r26, 1, 62
	add %r14, %r19, %r7
	lbz %r7, 0(%r14)
	lbz %r8, 1(%r14)
	rldicr %r8, %r8, 8, 55
	add %r7, %r7, %r8
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 32(%r6)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 33(%r6)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 34(%r6)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 35(%r6)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 36(%r6)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 37(%r6)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 38(%r6)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 39(%r6)
	rldicr %r8, %r7, 55, 8
	rldicl %r8, %r8, 1, 63
	stb %r8, 40(%r6)
	rldicr %r8, %r7, 54, 9
	rldicl %r8, %r8, 1, 63
	stb %r8, 41(%r6)
	rldicr %r8, %r7, 53, 10
	rldicl %r8, %r8, 1, 63
	stb %r8, 42(%r6)
	rldicr %r8, %r7, 52, 11
	rldicl %r8, %r8, 1, 63
	stb %r8, 43(%r6)
	rldicr %r8, %r7, 51, 12
	rldicl %r8, %r8, 1, 63
	stb %r8, 44(%r6)
	rldicr %r8, %r7, 50, 13
	rldicl %r8, %r8, 1, 63
	stb %r8, 45(%r6)
	rldicr %r8, %r7, 49, 14
	rldicl %r8, %r8, 1, 63
	stb %r8, 46(%r6)
	rldicr %r8, %r7, 48, 15
	rldicl %r8, %r8, 1, 63
	stb %r8, 47(%r6)
	li %r16, 16
233:
	addi %r16, %r16, -1
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	add %r7, %r6, %r16
	lbz %r7, 32(%r7)
	addi %r11, %r7, -1
	lwz %r5, 64(%r6)
	lwz %r7, 608(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 612(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 616(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 620(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 624(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 628(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 632(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 636(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 640(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 644(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 648(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 652(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 656(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 660(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 664(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 668(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 672(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 676(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 680(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 684(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 688(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 692(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 696(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 700(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 704(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 708(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 712(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 716(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 720(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 724(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 728(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 732(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 732(%r6)
	cmpldi %cr0, %r16, 0
	bne %cr0, 233b
	cmpldi %cr0, %r26, 0
	bne %cr0, 231b
	addi %r14, %r6, 8032
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	addi %r14, %r6, 7776
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	addi %r14, %r31, 0
	addi %r19, %r14, 0
	lis %r7, 4953
	ori %r7, %r7, 30883
	stw %r7, 576(%r6)
	lis %r7, 30187
	ori %r7, %r7, 19914
	stw %r7, 580(%r6)
	lis %r7, 16705
	ori %r7, %r7, 55467
	stw %r7, 584(%r6)
	lis %r7, 112
	ori %r7, %r7, 2637
	stw %r7, 588(%r6)
	lis %r7, 30585
	ori %r7, %r7, 59544
	stw %r7, 592(%r6)
	lis %r7, -29497
	ori %r7, %r7, 16505
	stw %r7, 596(%r6)
	lis %r7, 11119
	ori %r7, %r7, 65139
	stw %r7, 600(%r6)
	lis %r7, 20995
	ori %r7, %r7, 27886
	stw %r7, 604(%r6)
	li %r16, 0
234:
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	li %r15, 16
235:
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r15, %r15, -1
	cmpldi %cr0, %r15, 0
	bne %cr0, 235b
	addi %r16, %r16, 1
	addi %r7, %r16, -32
	cmpldi %cr0, %r7, 0
	bne %cr0, 234b
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
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
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 168(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 172(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 176(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 180(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 184(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 188(%r6)
	li %r26, 32
236:
	addi %r26, %r26, -1
	addi %r16, %r26, 0
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 1632
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	li %r16, 0
237:
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 64(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 68(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 72(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 76(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 80(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 84(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 88(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 92(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 96(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 100(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 104(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 108(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 112(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 116(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 120(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 124(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 128(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 132(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 136(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 140(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 144(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 148(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 152(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 156(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 160(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 108(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 112(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 116(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 120(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 124(%r14)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	addi %r16, %r16, 1
	addi %r7, %r16, -16
	cmpldi %cr0, %r7, 0
	bne %cr0, 237b
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	rldicr %r7, %r26, 1, 62
	add %r14, %r19, %r7
	lbz %r7, 0(%r14)
	lbz %r8, 1(%r14)
	rldicr %r8, %r8, 8, 55
	add %r7, %r7, %r8
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 32(%r6)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 33(%r6)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 34(%r6)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 35(%r6)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 36(%r6)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 37(%r6)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 38(%r6)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 39(%r6)
	rldicr %r8, %r7, 55, 8
	rldicl %r8, %r8, 1, 63
	stb %r8, 40(%r6)
	rldicr %r8, %r7, 54, 9
	rldicl %r8, %r8, 1, 63
	stb %r8, 41(%r6)
	rldicr %r8, %r7, 53, 10
	rldicl %r8, %r8, 1, 63
	stb %r8, 42(%r6)
	rldicr %r8, %r7, 52, 11
	rldicl %r8, %r8, 1, 63
	stb %r8, 43(%r6)
	rldicr %r8, %r7, 51, 12
	rldicl %r8, %r8, 1, 63
	stb %r8, 44(%r6)
	rldicr %r8, %r7, 50, 13
	rldicl %r8, %r8, 1, 63
	stb %r8, 45(%r6)
	rldicr %r8, %r7, 49, 14
	rldicl %r8, %r8, 1, 63
	stb %r8, 46(%r6)
	rldicr %r8, %r7, 48, 15
	rldicl %r8, %r8, 1, 63
	stb %r8, 47(%r6)
	li %r16, 16
238:
	addi %r16, %r16, -1
	lwz %r7, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 732(%r6)
	addi %r14, %r6, 5728
	rldicr %r7, %r16, 7, 56
	add %r14, %r14, %r7
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	lwz %r7, 608(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 612(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 616(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 620(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 624(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 628(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 632(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 636(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 640(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 644(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 648(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 652(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 656(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 660(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 664(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 668(%r6)
	stw %r7, 124(%r6)
	lwz %r7, 672(%r6)
	stw %r7, 128(%r6)
	lwz %r7, 676(%r6)
	stw %r7, 132(%r6)
	lwz %r7, 680(%r6)
	stw %r7, 136(%r6)
	lwz %r7, 684(%r6)
	stw %r7, 140(%r6)
	lwz %r7, 688(%r6)
	stw %r7, 144(%r6)
	lwz %r7, 692(%r6)
	stw %r7, 148(%r6)
	lwz %r7, 696(%r6)
	stw %r7, 152(%r6)
	lwz %r7, 700(%r6)
	stw %r7, 156(%r6)
	lwz %r7, 704(%r6)
	stw %r7, 160(%r6)
	lwz %r7, 708(%r6)
	stw %r7, 164(%r6)
	lwz %r7, 712(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 716(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 720(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 724(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 728(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 732(%r6)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	add %r7, %r6, %r16
	lbz %r7, 32(%r7)
	addi %r11, %r7, -1
	lwz %r5, 64(%r6)
	lwz %r7, 608(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 608(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 612(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 612(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 616(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 616(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 620(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 620(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 624(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 624(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 628(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 628(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 632(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 632(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 636(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 636(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 640(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 640(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 644(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 644(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 648(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 648(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 652(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 652(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 656(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 656(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 660(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 660(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 664(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 664(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 668(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 668(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 672(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 672(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 676(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 676(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 680(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 680(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 684(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 684(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 688(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 688(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 692(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 692(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 696(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 696(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 700(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 700(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 704(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 704(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 708(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 708(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 712(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 712(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 716(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 716(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 720(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 720(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 724(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 724(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 728(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 728(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 732(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 732(%r6)
	cmpldi %cr0, %r16, 0
	bne %cr0, 238b
	cmpldi %cr0, %r26, 0
	bne %cr0, 236b
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r14, %r6, 7904
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	bl {vg_ed25519_r32_point_add}
	addi %r6, %r3, 0
	lwz %r7, 64(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 68(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 72(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 76(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 80(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 84(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 88(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 92(%r6)
	stw %r7, 220(%r6)
	lwz %r7, 96(%r6)
	stw %r7, 224(%r6)
	lwz %r7, 100(%r6)
	stw %r7, 228(%r6)
	lwz %r7, 104(%r6)
	stw %r7, 232(%r6)
	lwz %r7, 108(%r6)
	stw %r7, 236(%r6)
	lwz %r7, 112(%r6)
	stw %r7, 240(%r6)
	lwz %r7, 116(%r6)
	stw %r7, 244(%r6)
	lwz %r7, 120(%r6)
	stw %r7, 248(%r6)
	lwz %r7, 124(%r6)
	stw %r7, 252(%r6)
	lwz %r7, 128(%r6)
	stw %r7, 256(%r6)
	lwz %r7, 132(%r6)
	stw %r7, 260(%r6)
	lwz %r7, 136(%r6)
	stw %r7, 264(%r6)
	lwz %r7, 140(%r6)
	stw %r7, 268(%r6)
	lwz %r7, 144(%r6)
	stw %r7, 272(%r6)
	lwz %r7, 148(%r6)
	stw %r7, 276(%r6)
	lwz %r7, 152(%r6)
	stw %r7, 280(%r6)
	lwz %r7, 156(%r6)
	stw %r7, 284(%r6)
	lwz %r7, 160(%r6)
	stw %r7, 288(%r6)
	lwz %r7, 164(%r6)
	stw %r7, 292(%r6)
	lwz %r7, 168(%r6)
	stw %r7, 296(%r6)
	lwz %r7, 172(%r6)
	stw %r7, 300(%r6)
	lwz %r7, 176(%r6)
	stw %r7, 304(%r6)
	lwz %r7, 180(%r6)
	stw %r7, 308(%r6)
	lwz %r7, 184(%r6)
	stw %r7, 312(%r6)
	lwz %r7, 188(%r6)
	stw %r7, 316(%r6)
	addi %r14, %r6, 8032
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	lwz %r7, 32(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 36(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 40(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 44(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 48(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 52(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 56(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 60(%r14)
	stw %r7, 124(%r6)
	lwz %r7, 64(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 68(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 72(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 76(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 80(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 84(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 88(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 92(%r14)
	stw %r7, 156(%r6)
	lwz %r7, 96(%r14)
	stw %r7, 160(%r6)
	lwz %r7, 100(%r14)
	stw %r7, 164(%r6)
	lwz %r7, 104(%r14)
	stw %r7, 168(%r6)
	lwz %r7, 108(%r14)
	stw %r7, 172(%r6)
	lwz %r7, 112(%r14)
	stw %r7, 176(%r6)
	lwz %r7, 116(%r14)
	stw %r7, 180(%r6)
	lwz %r7, 120(%r14)
	stw %r7, 184(%r6)
	lwz %r7, 124(%r14)
	stw %r7, 188(%r6)
	addi %r3, %r6, 0
	li %r4, 320
	li %r5, 64
	li %r6, 256
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 352
	li %r5, 192
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 384
	li %r5, 96
	li %r6, 256
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	addi %r3, %r6, 0
	li %r4, 416
	li %r5, 224
	li %r6, 128
	bl {vg_gf25519_r32_mul}
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 320(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 352(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 356(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 360(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 364(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 336(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 368(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 340(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 372(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 344(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 376(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 348(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 380(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 239f
	li %r17, 0
	b 240f
239:
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
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 420(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 424(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 428(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 432(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 436(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 440(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 444(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	lwz %r7, 736(%r6)
	stw %r7, 864(%r6)
	lwz %r7, 740(%r6)
	stw %r7, 868(%r6)
	lwz %r7, 744(%r6)
	stw %r7, 872(%r6)
	lwz %r7, 748(%r6)
	stw %r7, 876(%r6)
	lwz %r7, 752(%r6)
	stw %r7, 880(%r6)
	lwz %r7, 756(%r6)
	stw %r7, 884(%r6)
	lwz %r7, 760(%r6)
	stw %r7, 888(%r6)
	lwz %r7, 764(%r6)
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
	li %r5, 0
	lwz %r7, 864(%r6)
	add %r5, %r5, %r7
	lwz %r7, 868(%r6)
	add %r5, %r5, %r7
	lwz %r7, 872(%r6)
	add %r5, %r5, %r7
	lwz %r7, 876(%r6)
	add %r5, %r5, %r7
	lwz %r7, 880(%r6)
	add %r5, %r5, %r7
	lwz %r7, 884(%r6)
	add %r5, %r5, %r7
	lwz %r7, 888(%r6)
	add %r5, %r5, %r7
	lwz %r7, 892(%r6)
	add %r5, %r5, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 241f
	li %r17, 0
	b 242f
241:
	li %r17, 1
242:
240:
228:
21:
	ld %r7, 1120(%r6)
	mtlr %r7
	addi %r3, %r17, 0
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

vg_ed25519_verify:
	stdu %r1, -224(%r1)
	addi %r8, %r1, 32
	mflr %r0
	std %r20, 128(%r8)
	std %r21, 136(%r8)
	std %r22, 144(%r8)
	std %r23, 152(%r8)
	std %r24, 160(%r8)
	std %r25, 168(%r8)
	std %r0, 176(%r8)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r5, 0
	addi %r23, %r6, 0
	addi %r24, %r7, 0
	addi %r25, %r8, 0
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r23, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r20, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 64
	addi %r5, %r21, 0
	addi %r6, %r22, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r22, 64
	addi %r5, %r25, 64
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 0
	addi %r4, %r25, 64
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	li %r8, 0
	std %r8, 32(%r25)
	std %r8, 40(%r25)
	std %r8, 48(%r25)
	std %r8, 56(%r25)
	addi %r3, %r20, 0
	addi %r4, %r23, 0
	addi %r5, %r25, 0
	addi %r6, %r24, 0
	bl {vg_ed25519_verify_equation}
	ld %r0, 176(%r25)
	ld %r20, 128(%r25)
	ld %r21, 136(%r25)
	ld %r22, 144(%r25)
	ld %r23, 152(%r25)
	ld %r24, 160(%r25)
	ld %r25, 168(%r25)
	mtlr %r0
	addi %r1, %r1, 224
	blr
