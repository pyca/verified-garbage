// The functions of `src/internal/vg_ed448_scalar_mul_add.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_mul_add:
	std %r14, 1064(%r7)
	std %r15, 1072(%r7)
	std %r16, 1080(%r7)
	std %r17, 1088(%r7)
	std %r18, 1096(%r7)
	std %r19, 1104(%r7)
	std %r26, 1112(%r7)
	std %r27, 1120(%r7)
	std %r28, 1128(%r7)
	std %r29, 1136(%r7)
	std %r30, 1144(%r7)
	std %r31, 1152(%r7)
	addi %r27, %r3, 0
	addi %r26, %r4, 0
	addi %r17, %r6, 0
	addi %r6, %r7, 0
	addi %r14, %r5, 0
	li %r7, 0
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
	li %r15, 57
20:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
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
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 20b
	addi %r14, %r17, 0
	li %r7, 0
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
	li %r15, 57
21:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
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
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 21b
	addi %r14, %r26, 0
	li %r7, 0
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
	li %r15, 57
22:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 22b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
23:
	lwz %r4, 112(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 224(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 228(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 232(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 236(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 240(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 244(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 248(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 252(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 256(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 260(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 264(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 268(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 272(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 276(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1008(%r6)
	add %r7, %r7, %r8
	stw %r7, 1008(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1012(%r6)
	add %r7, %r7, %r8
	stw %r7, 1012(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1016(%r6)
	add %r7, %r7, %r8
	stw %r7, 1016(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1020(%r6)
	add %r7, %r7, %r8
	stw %r7, 1020(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1024(%r6)
	add %r7, %r7, %r8
	stw %r7, 1024(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1028(%r6)
	add %r7, %r7, %r8
	stw %r7, 1028(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1032(%r6)
	add %r7, %r7, %r8
	stw %r7, 1032(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1036(%r6)
	add %r7, %r7, %r8
	stw %r7, 1036(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1040(%r6)
	add %r7, %r7, %r8
	stw %r7, 1040(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1044(%r6)
	add %r7, %r7, %r8
	stw %r7, 1044(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1048(%r6)
	add %r7, %r7, %r8
	stw %r7, 1048(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1052(%r6)
	add %r7, %r7, %r8
	stw %r7, 1052(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1056(%r6)
	add %r7, %r7, %r8
	stw %r7, 1056(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1060(%r6)
	add %r7, %r7, %r8
	stw %r7, 1060(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r14, %r6, 280
	lwz %r7, 952(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 956(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 960(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 964(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 968(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 972(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 976(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 980(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 984(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 988(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 992(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 996(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 1000(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 1004(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 1008(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 1012(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 1016(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 1020(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 1024(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 1028(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 1032(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 1036(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 1040(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 1044(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 1048(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 1052(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 1056(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 1060(%r6)
	stw %r7, 108(%r14)
	li %r7, 0
	stw %r7, 0(%r6)
	stw %r7, 4(%r6)
	stw %r7, 8(%r6)
	stw %r7, 12(%r6)
	stw %r7, 16(%r6)
	stw %r7, 20(%r6)
	stw %r7, 24(%r6)
	stw %r7, 28(%r6)
	stw %r7, 32(%r6)
	stw %r7, 36(%r6)
	stw %r7, 40(%r6)
	stw %r7, 44(%r6)
	stw %r7, 48(%r6)
	stw %r7, 52(%r6)
	li %r15, 112
24:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 24b
	addi %r14, %r27, 0
	lwz %r7, 0(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 4(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 8(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 12(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 16(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 20(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 24(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 28(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 32(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 36(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 40(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 44(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 48(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 52(%r6)
	stw %r7, 52(%r14)
	li %r7, 0
	stb %r7, 56(%r14)
	ld %r14, 1064(%r6)
	ld %r15, 1072(%r6)
	ld %r16, 1080(%r6)
	ld %r17, 1088(%r6)
	ld %r18, 1096(%r6)
	ld %r19, 1104(%r6)
	ld %r26, 1112(%r6)
	ld %r27, 1120(%r6)
	ld %r28, 1128(%r6)
	ld %r29, 1136(%r6)
	ld %r30, 1144(%r6)
	ld %r31, 1152(%r6)
	blr
