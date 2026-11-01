// The functions of `src/internal/vg_sm3_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
