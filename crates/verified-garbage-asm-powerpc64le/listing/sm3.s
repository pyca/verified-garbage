// The functions of `src/sm3.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_compress:
	std %r14, 64(%r6)
	std %r15, 72(%r6)
	std %r16, 80(%r6)
	std %r17, 88(%r6)
	std %r18, 96(%r6)
	std %r19, 104(%r6)
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	lwz %r7, 0(%r3)
	lwz %r8, 4(%r3)
	lwz %r9, 8(%r3)
	lwz %r10, 12(%r3)
	lwz %r11, 16(%r3)
	lwz %r12, 20(%r3)
	lwz %r14, 24(%r3)
	lwz %r15, 28(%r3)
	li %r0, 0
	lwbrx %r16, %r4, %r0
	stw %r16, 0(%r6)
	li %r0, 4
	lwbrx %r16, %r4, %r0
	stw %r16, 4(%r6)
	li %r0, 8
	lwbrx %r16, %r4, %r0
	stw %r16, 8(%r6)
	li %r0, 12
	lwbrx %r16, %r4, %r0
	stw %r16, 12(%r6)
	li %r0, 16
	lwbrx %r16, %r4, %r0
	stw %r16, 16(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, 31180
	ori %r18, %r18, 17689
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 0(%r6)
	add %r15, %r15, %r18
	lwz %r19, 16(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	xor %r16, %r7, %r8
	xor %r16, %r16, %r9
	add %r10, %r10, %r16
	xor %r16, %r11, %r12
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	li %r0, 20
	lwbrx %r16, %r4, %r0
	stw %r16, 20(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -3176
	ori %r18, %r18, 35378
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 4(%r6)
	add %r14, %r14, %r18
	lwz %r19, 20(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	xor %r16, %r10, %r7
	xor %r16, %r16, %r8
	add %r9, %r9, %r16
	xor %r16, %r15, %r11
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	li %r0, 24
	lwbrx %r16, %r4, %r0
	stw %r16, 24(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -6351
	ori %r18, %r18, 5221
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 8(%r6)
	add %r12, %r12, %r18
	lwz %r19, 24(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	xor %r16, %r9, %r10
	xor %r16, %r16, %r7
	add %r8, %r8, %r16
	xor %r16, %r14, %r15
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	li %r0, 28
	lwbrx %r16, %r4, %r0
	stw %r16, 28(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -12702
	ori %r18, %r18, 10443
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 12(%r6)
	add %r11, %r11, %r18
	lwz %r19, 28(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	xor %r16, %r8, %r9
	xor %r16, %r16, %r10
	add %r7, %r7, %r16
	xor %r16, %r12, %r14
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	li %r0, 32
	lwbrx %r16, %r4, %r0
	stw %r16, 32(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -25404
	ori %r18, %r18, 20887
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 16(%r6)
	add %r15, %r15, %r18
	lwz %r19, 32(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	xor %r16, %r7, %r8
	xor %r16, %r16, %r9
	add %r10, %r10, %r16
	xor %r16, %r11, %r12
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	li %r0, 36
	lwbrx %r16, %r4, %r0
	stw %r16, 36(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 14728
	ori %r18, %r18, 41775
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 20(%r6)
	add %r14, %r14, %r18
	lwz %r19, 36(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	xor %r16, %r10, %r7
	xor %r16, %r16, %r8
	add %r9, %r9, %r16
	xor %r16, %r15, %r11
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	li %r0, 40
	lwbrx %r16, %r4, %r0
	stw %r16, 40(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 29457
	ori %r18, %r18, 18014
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 24(%r6)
	add %r12, %r12, %r18
	lwz %r19, 40(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	xor %r16, %r9, %r10
	xor %r16, %r16, %r7
	add %r8, %r8, %r16
	xor %r16, %r14, %r15
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	li %r0, 44
	lwbrx %r16, %r4, %r0
	stw %r16, 44(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -6622
	ori %r18, %r18, 36028
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 28(%r6)
	add %r11, %r11, %r18
	lwz %r19, 44(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	xor %r16, %r8, %r9
	xor %r16, %r16, %r10
	add %r7, %r7, %r16
	xor %r16, %r12, %r14
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	li %r0, 48
	lwbrx %r16, %r4, %r0
	stw %r16, 48(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -13243
	ori %r18, %r18, 6521
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 32(%r6)
	add %r15, %r15, %r18
	lwz %r19, 48(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	xor %r16, %r7, %r8
	xor %r16, %r16, %r9
	add %r10, %r10, %r16
	xor %r16, %r11, %r12
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	li %r0, 52
	lwbrx %r16, %r4, %r0
	stw %r16, 52(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -26486
	ori %r18, %r18, 13043
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 36(%r6)
	add %r14, %r14, %r18
	lwz %r19, 52(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	xor %r16, %r10, %r7
	xor %r16, %r16, %r8
	add %r9, %r9, %r16
	xor %r16, %r15, %r11
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	li %r0, 56
	lwbrx %r16, %r4, %r0
	stw %r16, 56(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 12564
	ori %r18, %r18, 26087
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 40(%r6)
	add %r12, %r12, %r18
	lwz %r19, 56(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	xor %r16, %r9, %r10
	xor %r16, %r16, %r7
	add %r8, %r8, %r16
	xor %r16, %r14, %r15
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	li %r0, 60
	lwbrx %r16, %r4, %r0
	stw %r16, 60(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 25128
	ori %r18, %r18, 52174
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 44(%r6)
	add %r11, %r11, %r18
	lwz %r19, 60(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	xor %r16, %r8, %r9
	xor %r16, %r16, %r10
	add %r7, %r7, %r16
	xor %r16, %r12, %r14
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 0(%r6)
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	stw %r16, 0(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -15279
	ori %r18, %r18, 38812
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 48(%r6)
	add %r15, %r15, %r18
	lwz %r19, 0(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	xor %r16, %r7, %r8
	xor %r16, %r16, %r9
	add %r10, %r10, %r16
	xor %r16, %r11, %r12
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 4(%r6)
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	stw %r16, 4(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -30557
	ori %r18, %r18, 12089
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 52(%r6)
	add %r14, %r14, %r18
	lwz %r19, 4(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	xor %r16, %r10, %r7
	xor %r16, %r16, %r8
	add %r9, %r9, %r16
	xor %r16, %r15, %r11
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 8(%r6)
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	stw %r16, 8(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 4422
	ori %r18, %r18, 24179
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 56(%r6)
	add %r12, %r12, %r18
	lwz %r19, 8(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	xor %r16, %r9, %r10
	xor %r16, %r16, %r7
	add %r8, %r8, %r16
	xor %r16, %r14, %r15
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 12(%r6)
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	stw %r16, 12(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 8844
	ori %r18, %r18, 48358
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 60(%r6)
	add %r11, %r11, %r18
	lwz %r19, 12(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	xor %r16, %r8, %r9
	xor %r16, %r16, %r10
	add %r7, %r7, %r16
	xor %r16, %r12, %r14
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 16(%r6)
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	stw %r16, 16(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -25206
	ori %r18, %r18, 31367
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 0(%r6)
	add %r15, %r15, %r18
	lwz %r19, 16(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 20(%r6)
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	stw %r16, 20(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 15124
	ori %r18, %r18, 62735
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 4(%r6)
	add %r14, %r14, %r18
	lwz %r19, 20(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 24(%r6)
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	stw %r16, 24(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 30249
	ori %r18, %r18, 59934
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 8(%r6)
	add %r12, %r12, %r18
	lwz %r19, 24(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 28(%r6)
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	stw %r16, 28(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -5037
	ori %r18, %r18, 54332
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 12(%r6)
	add %r11, %r11, %r18
	lwz %r19, 28(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 32(%r6)
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	stw %r16, 32(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -10073
	ori %r18, %r18, 43129
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 16(%r6)
	add %r15, %r15, %r18
	lwz %r19, 32(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 36(%r6)
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	stw %r16, 36(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -20145
	ori %r18, %r18, 20723
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 20(%r6)
	add %r14, %r14, %r18
	lwz %r19, 36(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 40(%r6)
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	stw %r16, 40(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 25246
	ori %r18, %r18, 41447
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 24(%r6)
	add %r12, %r12, %r18
	lwz %r19, 40(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 44(%r6)
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	stw %r16, 44(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -15043
	ori %r18, %r18, 17358
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 28(%r6)
	add %r11, %r11, %r18
	lwz %r19, 44(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 48(%r6)
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	stw %r16, 48(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -30086
	ori %r18, %r18, 34717
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 32(%r6)
	add %r15, %r15, %r18
	lwz %r19, 48(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 52(%r6)
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	stw %r16, 52(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 5365
	ori %r18, %r18, 3899
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 36(%r6)
	add %r14, %r14, %r18
	lwz %r19, 52(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 56(%r6)
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	stw %r16, 56(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 10730
	ori %r18, %r18, 7798
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 40(%r6)
	add %r12, %r12, %r18
	lwz %r19, 56(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 60(%r6)
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	stw %r16, 60(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 21460
	ori %r18, %r18, 15596
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 44(%r6)
	add %r11, %r11, %r18
	lwz %r19, 60(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 0(%r6)
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	stw %r16, 0(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -22616
	ori %r18, %r18, 31192
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 48(%r6)
	add %r15, %r15, %r18
	lwz %r19, 0(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 4(%r6)
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	stw %r16, 4(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 20304
	ori %r18, %r18, 62385
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 52(%r6)
	add %r14, %r14, %r18
	lwz %r19, 4(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 8(%r6)
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	stw %r16, 8(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -24927
	ori %r18, %r18, 59234
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 56(%r6)
	add %r12, %r12, %r18
	lwz %r19, 8(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 12(%r6)
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	stw %r16, 12(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 15683
	ori %r18, %r18, 52933
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 60(%r6)
	add %r11, %r11, %r18
	lwz %r19, 12(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 16(%r6)
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	stw %r16, 16(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, 31367
	ori %r18, %r18, 40330
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 0(%r6)
	add %r15, %r15, %r18
	lwz %r19, 16(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 20(%r6)
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	stw %r16, 20(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -2801
	ori %r18, %r18, 15124
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 4(%r6)
	add %r14, %r14, %r18
	lwz %r19, 20(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 24(%r6)
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	stw %r16, 24(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -5602
	ori %r18, %r18, 30249
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 8(%r6)
	add %r12, %r12, %r18
	lwz %r19, 24(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 28(%r6)
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	stw %r16, 28(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -11204
	ori %r18, %r18, 60499
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 12(%r6)
	add %r11, %r11, %r18
	lwz %r19, 28(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 32(%r6)
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	stw %r16, 32(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -22407
	ori %r18, %r18, 55463
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 16(%r6)
	add %r15, %r15, %r18
	lwz %r19, 32(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 36(%r6)
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	stw %r16, 36(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 20723
	ori %r18, %r18, 45391
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 20(%r6)
	add %r14, %r14, %r18
	lwz %r19, 36(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 40(%r6)
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	stw %r16, 40(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -24089
	ori %r18, %r18, 25246
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 24(%r6)
	add %r12, %r12, %r18
	lwz %r19, 40(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 44(%r6)
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	stw %r16, 44(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 17358
	ori %r18, %r18, 50493
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 28(%r6)
	add %r11, %r11, %r18
	lwz %r19, 44(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 48(%r6)
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	stw %r16, 48(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -30819
	ori %r18, %r18, 35450
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 32(%r6)
	add %r15, %r15, %r18
	lwz %r19, 48(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 52(%r6)
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	stw %r16, 52(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 3899
	ori %r18, %r18, 5365
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 36(%r6)
	add %r14, %r14, %r18
	lwz %r19, 52(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 56(%r6)
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	stw %r16, 56(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 7798
	ori %r18, %r18, 10730
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 40(%r6)
	add %r12, %r12, %r18
	lwz %r19, 56(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 60(%r6)
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	stw %r16, 60(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 15596
	ori %r18, %r18, 21460
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 44(%r6)
	add %r11, %r11, %r18
	lwz %r19, 60(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 0(%r6)
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	stw %r16, 0(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, 31192
	ori %r18, %r18, 42920
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 48(%r6)
	add %r15, %r15, %r18
	lwz %r19, 0(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 4(%r6)
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	stw %r16, 4(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -3151
	ori %r18, %r18, 20304
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 52(%r6)
	add %r14, %r14, %r18
	lwz %r19, 4(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 8(%r6)
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	stw %r16, 8(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -6302
	ori %r18, %r18, 40609
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 56(%r6)
	add %r12, %r12, %r18
	lwz %r19, 8(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 12(%r6)
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	stw %r16, 12(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -12603
	ori %r18, %r18, 15683
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 60(%r6)
	add %r11, %r11, %r18
	lwz %r19, 12(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 16(%r6)
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	stw %r16, 16(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -25206
	ori %r18, %r18, 31367
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 0(%r6)
	add %r15, %r15, %r18
	lwz %r19, 16(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 20(%r6)
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	stw %r16, 20(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 15124
	ori %r18, %r18, 62735
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 4(%r6)
	add %r14, %r14, %r18
	lwz %r19, 20(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 24(%r6)
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	stw %r16, 24(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 30249
	ori %r18, %r18, 59934
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 8(%r6)
	add %r12, %r12, %r18
	lwz %r19, 24(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 28(%r6)
	lwz %r17, 56(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	stw %r16, 28(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -5037
	ori %r18, %r18, 54332
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 12(%r6)
	add %r11, %r11, %r18
	lwz %r19, 28(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 32(%r6)
	lwz %r17, 60(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	stw %r16, 32(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -10073
	ori %r18, %r18, 43129
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 16(%r6)
	add %r15, %r15, %r18
	lwz %r19, 32(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 36(%r6)
	lwz %r17, 0(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	stw %r16, 36(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, -20145
	ori %r18, %r18, 20723
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 20(%r6)
	add %r14, %r14, %r18
	lwz %r19, 36(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 40(%r6)
	lwz %r17, 4(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	stw %r16, 40(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 25246
	ori %r18, %r18, 41447
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 24(%r6)
	add %r12, %r12, %r18
	lwz %r19, 40(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 44(%r6)
	lwz %r17, 8(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	stw %r16, 44(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, -15043
	ori %r18, %r18, 17358
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 28(%r6)
	add %r11, %r11, %r18
	lwz %r19, 44(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 48(%r6)
	lwz %r17, 12(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	stw %r16, 48(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -30086
	ori %r18, %r18, 34717
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 32(%r6)
	add %r15, %r15, %r18
	lwz %r19, 48(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 52(%r6)
	lwz %r17, 16(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	stw %r16, 52(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 5365
	ori %r18, %r18, 3899
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 36(%r6)
	add %r14, %r14, %r18
	lwz %r19, 52(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 56(%r6)
	lwz %r17, 20(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 4(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	stw %r16, 56(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, 10730
	ori %r18, %r18, 7798
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 40(%r6)
	add %r12, %r12, %r18
	lwz %r19, 56(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 60(%r6)
	lwz %r17, 24(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 8(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	stw %r16, 60(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 21460
	ori %r18, %r18, 15596
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 44(%r6)
	add %r11, %r11, %r18
	lwz %r19, 60(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 0(%r6)
	lwz %r17, 28(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 12(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	stw %r16, 0(%r6)
	rlwinm %r16, %r7, 12, 0, 31
	add %r17, %r16, %r11
	lis %r18, -22616
	ori %r18, %r18, 31192
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r15, %r15, %r17
	xor %r16, %r16, %r17
	add %r10, %r10, %r16
	lwz %r18, 48(%r6)
	add %r15, %r15, %r18
	lwz %r19, 0(%r6)
	xor %r19, %r18, %r19
	add %r10, %r10, %r19
	or %r16, %r7, %r8
	and %r16, %r16, %r9
	and %r17, %r7, %r8
	or %r16, %r16, %r17
	add %r10, %r10, %r16
	xor %r16, %r12, %r14
	and %r16, %r16, %r11
	xor %r16, %r16, %r14
	add %r15, %r15, %r16
	rlwinm %r8, %r8, 9, 0, 31
	rlwinm %r12, %r12, 19, 0, 31
	rlwinm %r16, %r15, 9, 0, 31
	rlwinm %r17, %r15, 17, 0, 31
	xor %r15, %r15, %r16
	xor %r15, %r15, %r17
	lwz %r16, 4(%r6)
	lwz %r17, 32(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 56(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 16(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 44(%r6)
	xor %r16, %r16, %r17
	stw %r16, 4(%r6)
	rlwinm %r16, %r10, 12, 0, 31
	add %r17, %r16, %r15
	lis %r18, 20304
	ori %r18, %r18, 62385
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r14, %r14, %r17
	xor %r16, %r16, %r17
	add %r9, %r9, %r16
	lwz %r18, 52(%r6)
	add %r14, %r14, %r18
	lwz %r19, 4(%r6)
	xor %r19, %r18, %r19
	add %r9, %r9, %r19
	or %r16, %r10, %r7
	and %r16, %r16, %r8
	and %r17, %r10, %r7
	or %r16, %r16, %r17
	add %r9, %r9, %r16
	xor %r16, %r11, %r12
	and %r16, %r16, %r15
	xor %r16, %r16, %r12
	add %r14, %r14, %r16
	rlwinm %r7, %r7, 9, 0, 31
	rlwinm %r11, %r11, 19, 0, 31
	rlwinm %r16, %r14, 9, 0, 31
	rlwinm %r17, %r14, 17, 0, 31
	xor %r14, %r14, %r16
	xor %r14, %r14, %r17
	lwz %r16, 8(%r6)
	lwz %r17, 36(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 60(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 20(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 48(%r6)
	xor %r16, %r16, %r17
	stw %r16, 8(%r6)
	rlwinm %r16, %r9, 12, 0, 31
	add %r17, %r16, %r14
	lis %r18, -24927
	ori %r18, %r18, 59234
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r12, %r12, %r17
	xor %r16, %r16, %r17
	add %r8, %r8, %r16
	lwz %r18, 56(%r6)
	add %r12, %r12, %r18
	lwz %r19, 8(%r6)
	xor %r19, %r18, %r19
	add %r8, %r8, %r19
	or %r16, %r9, %r10
	and %r16, %r16, %r7
	and %r17, %r9, %r10
	or %r16, %r16, %r17
	add %r8, %r8, %r16
	xor %r16, %r15, %r11
	and %r16, %r16, %r14
	xor %r16, %r16, %r11
	add %r12, %r12, %r16
	rlwinm %r10, %r10, 9, 0, 31
	rlwinm %r15, %r15, 19, 0, 31
	rlwinm %r16, %r12, 9, 0, 31
	rlwinm %r17, %r12, 17, 0, 31
	xor %r12, %r12, %r16
	xor %r12, %r12, %r17
	lwz %r16, 12(%r6)
	lwz %r17, 40(%r6)
	xor %r16, %r16, %r17
	lwz %r17, 0(%r6)
	rlwinm %r17, %r17, 15, 0, 31
	xor %r16, %r16, %r17
	rlwinm %r17, %r16, 15, 0, 31
	rlwinm %r18, %r16, 23, 0, 31
	xor %r16, %r16, %r17
	xor %r16, %r16, %r18
	lwz %r17, 24(%r6)
	rlwinm %r17, %r17, 7, 0, 31
	xor %r16, %r16, %r17
	lwz %r17, 52(%r6)
	xor %r16, %r16, %r17
	stw %r16, 12(%r6)
	rlwinm %r16, %r8, 12, 0, 31
	add %r17, %r16, %r12
	lis %r18, 15683
	ori %r18, %r18, 52933
	add %r17, %r17, %r18
	rlwinm %r17, %r17, 7, 0, 31
	add %r11, %r11, %r17
	xor %r16, %r16, %r17
	add %r7, %r7, %r16
	lwz %r18, 60(%r6)
	add %r11, %r11, %r18
	lwz %r19, 12(%r6)
	xor %r19, %r18, %r19
	add %r7, %r7, %r19
	or %r16, %r8, %r9
	and %r16, %r16, %r10
	and %r17, %r8, %r9
	or %r16, %r16, %r17
	add %r7, %r7, %r16
	xor %r16, %r14, %r15
	and %r16, %r16, %r12
	xor %r16, %r16, %r15
	add %r11, %r11, %r16
	rlwinm %r9, %r9, 9, 0, 31
	rlwinm %r14, %r14, 19, 0, 31
	rlwinm %r16, %r11, 9, 0, 31
	rlwinm %r17, %r11, 17, 0, 31
	xor %r11, %r11, %r16
	xor %r11, %r11, %r17
	lwz %r16, 0(%r3)
	lwz %r17, 4(%r3)
	lwz %r18, 8(%r3)
	lwz %r19, 12(%r3)
	xor %r7, %r7, %r16
	xor %r8, %r8, %r17
	xor %r9, %r9, %r18
	xor %r10, %r10, %r19
	lwz %r16, 16(%r3)
	lwz %r17, 20(%r3)
	lwz %r18, 24(%r3)
	lwz %r19, 28(%r3)
	xor %r11, %r11, %r16
	xor %r12, %r12, %r17
	xor %r14, %r14, %r18
	xor %r15, %r15, %r19
	stw %r7, 0(%r3)
	stw %r8, 4(%r3)
	stw %r9, 8(%r3)
	stw %r10, 12(%r3)
	stw %r11, 16(%r3)
	stw %r12, 20(%r3)
	stw %r14, 24(%r3)
	stw %r15, 28(%r3)
	addi %r4, %r4, 64
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 64(%r6)
	ld %r15, 72(%r6)
	ld %r16, 80(%r6)
	ld %r17, 88(%r6)
	ld %r18, 96(%r6)
	ld %r19, 104(%r6)
	blr

vg_sm3_init:
	lis %r8, 29568
	ori %r8, %r8, 5743
	stw %r8, 0(%r3)
	lis %r8, 18708
	ori %r8, %r8, 45753
	stw %r8, 4(%r3)
	lis %r8, 5924
	ori %r8, %r8, 17111
	stw %r8, 8(%r3)
	lis %r8, -9590
	ori %r8, %r8, 1536
	stw %r8, 12(%r3)
	lis %r8, -22161
	ori %r8, %r8, 12476
	stw %r8, 16(%r3)
	lis %r8, 5681
	ori %r8, %r8, 14506
	stw %r8, 20(%r3)
	lis %r8, -7283
	ori %r8, %r8, 61005
	stw %r8, 24(%r3)
	lis %r8, -20229
	ori %r8, %r8, 3662
	stw %r8, 28(%r3)
	blr

vg_sm3_update:
	stdu %r1, -192(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 112(%r7)
	std %r27, 120(%r7)
	std %r28, 128(%r7)
	std %r29, 136(%r7)
	std %r30, 144(%r7)
	std %r31, 152(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 63
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
211:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 32(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	b 210f
29:
210:
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
214:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 214b
	b 213f
212:
213:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 215f
	b 216f
215:
	addi %r4, %r26, 32
	li %r30, 0
	li %r9, 1
216:
	b 24f
23:
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 217f
	addi %r4, %r28, 0
	rldicl %r9, %r29, 58, 6
	rldicr %r8, %r9, 6, 57
	add %r28, %r28, %r8
	subf %r29, %r8, %r29
	b 218f
217:
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 221f
	b 222f
221:
	addi %r10, %r29, 0
222:
220:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 223f
225:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 32(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 225b
	b 224f
223:
224:
	cmpldi %cr0, %r10, 0
	beq %cr0, 226f
228:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 228b
	b 227f
226:
227:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 229f
	b 230f
229:
	addi %r4, %r26, 32
	li %r30, 0
	li %r9, 1
230:
218:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r3, %r26, 0
	addi %r5, %r9, 0
	addi %r6, %r27, 0
	bl {vg_sm3_compress}
	b 232f
231:
232:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 192
	blr

vg_sm3_finalize:
	stdu %r1, -192(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 112(%r6)
	std %r27, 120(%r6)
	std %r28, 128(%r6)
	std %r29, 136(%r6)
	std %r30, 144(%r6)
	std %r31, 152(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 63
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 7
	rldicl %r31, %r31, 58, 6
20:
	li %r10, 64
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 56
22:
	li %r8, 0
	subf %r10, %r30, %r10
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	std %r8, 32(%r11)
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
28:
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 28b
	b 27f
26:
27:
	cmpldi %cr0, %r31, 0
	beq %cr0, 29f
	b 210f
29:
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
	stdbrx %r8, %r26, %r11
210:
	addi %r4, %r26, 32
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sm3_compress}
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 192
	blr
