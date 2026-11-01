// The functions of `src/sha1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress:
	std %r14, 64(%r6)
	std %r15, 72(%r6)
	std %r16, 80(%r6)
	std %r17, 88(%r6)
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	lwz %r7, 0(%r3)
	lwz %r8, 4(%r3)
	lwz %r9, 8(%r3)
	lwz %r10, 12(%r3)
	lwz %r11, 16(%r3)
	lis %r14, 23170
	ori %r14, %r14, 31129
	li %r0, 0
	lwbrx %r15, %r4, %r0
	stw %r15, 0(%r6)
	add %r11, %r11, %r15
	xor %r0, %r9, %r10
	and %r0, %r0, %r8
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	li %r0, 4
	lwbrx %r16, %r4, %r0
	stw %r16, 4(%r6)
	add %r10, %r10, %r16
	xor %r0, %r8, %r9
	and %r0, %r0, %r7
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	li %r0, 8
	lwbrx %r17, %r4, %r0
	stw %r17, 8(%r6)
	add %r9, %r9, %r17
	xor %r0, %r7, %r8
	and %r0, %r0, %r11
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	li %r0, 12
	lwbrx %r15, %r4, %r0
	stw %r15, 12(%r6)
	add %r8, %r8, %r15
	xor %r0, %r11, %r7
	and %r0, %r0, %r10
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	li %r0, 16
	lwbrx %r16, %r4, %r0
	stw %r16, 16(%r6)
	add %r7, %r7, %r16
	xor %r0, %r10, %r11
	and %r0, %r0, %r9
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	li %r0, 20
	lwbrx %r17, %r4, %r0
	stw %r17, 20(%r6)
	add %r11, %r11, %r17
	xor %r0, %r9, %r10
	and %r0, %r0, %r8
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	li %r0, 24
	lwbrx %r15, %r4, %r0
	stw %r15, 24(%r6)
	add %r10, %r10, %r15
	xor %r0, %r8, %r9
	and %r0, %r0, %r7
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	li %r0, 28
	lwbrx %r16, %r4, %r0
	stw %r16, 28(%r6)
	add %r9, %r9, %r16
	xor %r0, %r7, %r8
	and %r0, %r0, %r11
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	li %r0, 32
	lwbrx %r17, %r4, %r0
	stw %r17, 32(%r6)
	add %r8, %r8, %r17
	xor %r0, %r11, %r7
	and %r0, %r0, %r10
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	li %r0, 36
	lwbrx %r15, %r4, %r0
	stw %r15, 36(%r6)
	add %r7, %r7, %r15
	xor %r0, %r10, %r11
	and %r0, %r0, %r9
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	li %r0, 40
	lwbrx %r16, %r4, %r0
	stw %r16, 40(%r6)
	add %r11, %r11, %r16
	xor %r0, %r9, %r10
	and %r0, %r0, %r8
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	li %r0, 44
	lwbrx %r17, %r4, %r0
	stw %r17, 44(%r6)
	add %r10, %r10, %r17
	xor %r0, %r8, %r9
	and %r0, %r0, %r7
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	li %r0, 48
	lwbrx %r15, %r4, %r0
	stw %r15, 48(%r6)
	add %r9, %r9, %r15
	xor %r0, %r7, %r8
	and %r0, %r0, %r11
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	li %r0, 52
	lwbrx %r16, %r4, %r0
	stw %r16, 52(%r6)
	add %r8, %r8, %r16
	xor %r0, %r11, %r7
	and %r0, %r0, %r10
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	li %r0, 56
	lwbrx %r17, %r4, %r0
	stw %r17, 56(%r6)
	add %r7, %r7, %r17
	xor %r0, %r10, %r11
	and %r0, %r0, %r9
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	li %r0, 60
	lwbrx %r15, %r4, %r0
	stw %r15, 60(%r6)
	add %r11, %r11, %r15
	xor %r0, %r9, %r10
	and %r0, %r0, %r8
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 32(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 8(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 0(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 0(%r6)
	add %r10, %r10, %r16
	xor %r0, %r8, %r9
	and %r0, %r0, %r7
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 36(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 12(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 4(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 4(%r6)
	add %r9, %r9, %r17
	xor %r0, %r7, %r8
	and %r0, %r0, %r11
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 40(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 16(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 8(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 8(%r6)
	add %r8, %r8, %r15
	xor %r0, %r11, %r7
	and %r0, %r0, %r10
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 44(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 20(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 12(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 12(%r6)
	add %r7, %r7, %r16
	xor %r0, %r10, %r11
	and %r0, %r0, %r9
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lis %r14, 28377
	ori %r14, %r14, 60321
	lwz %r12, 48(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 24(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 16(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 16(%r6)
	add %r11, %r11, %r17
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 52(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 28(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 20(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 20(%r6)
	add %r10, %r10, %r15
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 56(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 32(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 24(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 24(%r6)
	add %r9, %r9, %r16
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 60(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 36(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 28(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 28(%r6)
	add %r8, %r8, %r17
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 0(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 40(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 32(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 32(%r6)
	add %r7, %r7, %r15
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 4(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 44(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 36(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 36(%r6)
	add %r11, %r11, %r16
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 8(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 48(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 40(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 40(%r6)
	add %r10, %r10, %r17
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 12(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 52(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 44(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 44(%r6)
	add %r9, %r9, %r15
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 16(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 56(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 48(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 48(%r6)
	add %r8, %r8, %r16
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 20(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 60(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 52(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 52(%r6)
	add %r7, %r7, %r17
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 24(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 0(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 56(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 56(%r6)
	add %r11, %r11, %r15
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 28(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 4(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 60(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 60(%r6)
	add %r10, %r10, %r16
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 32(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 8(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 0(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 0(%r6)
	add %r9, %r9, %r17
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 36(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 12(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 4(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 4(%r6)
	add %r8, %r8, %r15
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 40(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 16(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 8(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 8(%r6)
	add %r7, %r7, %r16
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 44(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 20(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 12(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 12(%r6)
	add %r11, %r11, %r17
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 48(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 24(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 16(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 16(%r6)
	add %r10, %r10, %r15
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 52(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 28(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 20(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 20(%r6)
	add %r9, %r9, %r16
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 56(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 32(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 24(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 24(%r6)
	add %r8, %r8, %r17
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 60(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 36(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 28(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 28(%r6)
	add %r7, %r7, %r15
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lis %r14, -28901
	ori %r14, %r14, 48348
	lwz %r12, 0(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 40(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 32(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 32(%r6)
	add %r11, %r11, %r16
	or %r0, %r8, %r9
	and %r0, %r0, %r10
	and %r12, %r8, %r9
	or %r0, %r0, %r12
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 4(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 44(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 36(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 36(%r6)
	add %r10, %r10, %r17
	or %r0, %r7, %r8
	and %r0, %r0, %r9
	and %r12, %r7, %r8
	or %r0, %r0, %r12
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 8(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 48(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 40(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 40(%r6)
	add %r9, %r9, %r15
	or %r0, %r11, %r7
	and %r0, %r0, %r8
	and %r12, %r11, %r7
	or %r0, %r0, %r12
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 12(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 52(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 44(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 44(%r6)
	add %r8, %r8, %r16
	or %r0, %r10, %r11
	and %r0, %r0, %r7
	and %r12, %r10, %r11
	or %r0, %r0, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 16(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 56(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 48(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 48(%r6)
	add %r7, %r7, %r17
	or %r0, %r9, %r10
	and %r0, %r0, %r11
	and %r12, %r9, %r10
	or %r0, %r0, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 20(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 60(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 52(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 52(%r6)
	add %r11, %r11, %r15
	or %r0, %r8, %r9
	and %r0, %r0, %r10
	and %r12, %r8, %r9
	or %r0, %r0, %r12
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 24(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 0(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 56(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 56(%r6)
	add %r10, %r10, %r16
	or %r0, %r7, %r8
	and %r0, %r0, %r9
	and %r12, %r7, %r8
	or %r0, %r0, %r12
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 28(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 4(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 60(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 60(%r6)
	add %r9, %r9, %r17
	or %r0, %r11, %r7
	and %r0, %r0, %r8
	and %r12, %r11, %r7
	or %r0, %r0, %r12
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 32(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 8(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 0(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 0(%r6)
	add %r8, %r8, %r15
	or %r0, %r10, %r11
	and %r0, %r0, %r7
	and %r12, %r10, %r11
	or %r0, %r0, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 36(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 12(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 4(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 4(%r6)
	add %r7, %r7, %r16
	or %r0, %r9, %r10
	and %r0, %r0, %r11
	and %r12, %r9, %r10
	or %r0, %r0, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 40(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 16(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 8(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 8(%r6)
	add %r11, %r11, %r17
	or %r0, %r8, %r9
	and %r0, %r0, %r10
	and %r12, %r8, %r9
	or %r0, %r0, %r12
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 44(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 20(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 12(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 12(%r6)
	add %r10, %r10, %r15
	or %r0, %r7, %r8
	and %r0, %r0, %r9
	and %r12, %r7, %r8
	or %r0, %r0, %r12
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 48(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 24(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 16(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 16(%r6)
	add %r9, %r9, %r16
	or %r0, %r11, %r7
	and %r0, %r0, %r8
	and %r12, %r11, %r7
	or %r0, %r0, %r12
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 52(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 28(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 20(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 20(%r6)
	add %r8, %r8, %r17
	or %r0, %r10, %r11
	and %r0, %r0, %r7
	and %r12, %r10, %r11
	or %r0, %r0, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 56(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 32(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 24(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 24(%r6)
	add %r7, %r7, %r15
	or %r0, %r9, %r10
	and %r0, %r0, %r11
	and %r12, %r9, %r10
	or %r0, %r0, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 60(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 36(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 28(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 28(%r6)
	add %r11, %r11, %r16
	or %r0, %r8, %r9
	and %r0, %r0, %r10
	and %r12, %r8, %r9
	or %r0, %r0, %r12
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 0(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 40(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 32(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 32(%r6)
	add %r10, %r10, %r17
	or %r0, %r7, %r8
	and %r0, %r0, %r9
	and %r12, %r7, %r8
	or %r0, %r0, %r12
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 4(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 44(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 36(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 36(%r6)
	add %r9, %r9, %r15
	or %r0, %r11, %r7
	and %r0, %r0, %r8
	and %r12, %r11, %r7
	or %r0, %r0, %r12
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 8(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 48(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 40(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 40(%r6)
	add %r8, %r8, %r16
	or %r0, %r10, %r11
	and %r0, %r0, %r7
	and %r12, %r10, %r11
	or %r0, %r0, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 12(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 52(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 44(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 44(%r6)
	add %r7, %r7, %r17
	or %r0, %r9, %r10
	and %r0, %r0, %r11
	and %r12, %r9, %r10
	or %r0, %r0, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lis %r14, -13726
	ori %r14, %r14, 49622
	lwz %r12, 16(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 56(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 48(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 48(%r6)
	add %r11, %r11, %r15
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 20(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 60(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 52(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 52(%r6)
	add %r10, %r10, %r16
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 24(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 0(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 56(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 56(%r6)
	add %r9, %r9, %r17
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 28(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 4(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 60(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 60(%r6)
	add %r8, %r8, %r15
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 32(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 8(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 0(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 0(%r6)
	add %r7, %r7, %r16
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 36(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 12(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 4(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 4(%r6)
	add %r11, %r11, %r17
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 40(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 16(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 8(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 8(%r6)
	add %r10, %r10, %r15
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 44(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 20(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 12(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 12(%r6)
	add %r9, %r9, %r16
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 48(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 24(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 16(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 16(%r6)
	add %r8, %r8, %r17
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 52(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 28(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 20(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 20(%r6)
	add %r7, %r7, %r15
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 56(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 32(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 24(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 24(%r6)
	add %r11, %r11, %r16
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 60(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 36(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 28(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 28(%r6)
	add %r10, %r10, %r17
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 0(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 40(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 32(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 32(%r6)
	add %r9, %r9, %r15
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 4(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 44(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 36(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 36(%r6)
	add %r8, %r8, %r16
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 8(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 48(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 40(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 40(%r6)
	add %r7, %r7, %r17
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 12(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 52(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 44(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 44(%r6)
	add %r11, %r11, %r15
	xor %r0, %r8, %r9
	xor %r0, %r0, %r10
	add %r11, %r11, %r0
	add %r11, %r11, %r14
	rlwinm %r0, %r7, 5, 0, 31
	add %r11, %r11, %r0
	rlwinm %r8, %r8, 30, 0, 31
	lwz %r12, 16(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 56(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 48(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 48(%r6)
	add %r10, %r10, %r16
	xor %r0, %r7, %r8
	xor %r0, %r0, %r9
	add %r10, %r10, %r0
	add %r10, %r10, %r14
	rlwinm %r0, %r11, 5, 0, 31
	add %r10, %r10, %r0
	rlwinm %r7, %r7, 30, 0, 31
	lwz %r12, 20(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 60(%r6)
	xor %r17, %r17, %r12
	lwz %r12, 52(%r6)
	xor %r17, %r17, %r12
	rlwinm %r17, %r17, 1, 0, 31
	stw %r17, 52(%r6)
	add %r9, %r9, %r17
	xor %r0, %r11, %r7
	xor %r0, %r0, %r8
	add %r9, %r9, %r0
	add %r9, %r9, %r14
	rlwinm %r0, %r10, 5, 0, 31
	add %r9, %r9, %r0
	rlwinm %r11, %r11, 30, 0, 31
	lwz %r12, 24(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 0(%r6)
	xor %r15, %r15, %r12
	lwz %r12, 56(%r6)
	xor %r15, %r15, %r12
	rlwinm %r15, %r15, 1, 0, 31
	stw %r15, 56(%r6)
	add %r8, %r8, %r15
	xor %r0, %r10, %r11
	xor %r0, %r0, %r7
	add %r8, %r8, %r0
	add %r8, %r8, %r14
	rlwinm %r0, %r9, 5, 0, 31
	add %r8, %r8, %r0
	rlwinm %r10, %r10, 30, 0, 31
	lwz %r12, 28(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 4(%r6)
	xor %r16, %r16, %r12
	lwz %r12, 60(%r6)
	xor %r16, %r16, %r12
	rlwinm %r16, %r16, 1, 0, 31
	stw %r16, 60(%r6)
	add %r7, %r7, %r16
	xor %r0, %r9, %r10
	xor %r0, %r0, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r14
	rlwinm %r0, %r8, 5, 0, 31
	add %r7, %r7, %r0
	rlwinm %r9, %r9, 30, 0, 31
	lwz %r12, 0(%r3)
	add %r7, %r7, %r12
	lwz %r12, 4(%r3)
	add %r8, %r8, %r12
	lwz %r12, 8(%r3)
	add %r9, %r9, %r12
	lwz %r12, 12(%r3)
	add %r10, %r10, %r12
	lwz %r12, 16(%r3)
	add %r11, %r11, %r12
	stw %r7, 0(%r3)
	stw %r8, 4(%r3)
	stw %r9, 8(%r3)
	stw %r10, 12(%r3)
	stw %r11, 16(%r3)
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
	blr

vg_sha1_init:
	lis %r8, 26437
	ori %r8, %r8, 8961
	stw %r8, 0(%r3)
	lis %r8, -4147
	ori %r8, %r8, 43913
	stw %r8, 4(%r3)
	lis %r8, -26438
	ori %r8, %r8, 56574
	stw %r8, 8(%r3)
	lis %r8, 4146
	ori %r8, %r8, 21622
	stw %r8, 12(%r3)
	lis %r8, -15406
	ori %r8, %r8, 57840
	stw %r8, 16(%r3)
	blr

vg_sha1_update:
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	addi %r4, %r26, 20
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	addi %r4, %r26, 20
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
	bl {vg_sha1_compress}
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

vg_sha1_finalize:
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
	stb %r8, 20(%r11)
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	li %r11, 76
	stdbrx %r8, %r26, %r11
210:
	addi %r4, %r26, 20
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
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

vg_sha1_update_scratch:
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	addi %r4, %r26, 20
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	addi %r4, %r26, 20
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
	bl {vg_sha1_compress}
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
	blr

vg_sha1_finalize_scratch:
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
	stb %r8, 20(%r11)
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
	std %r8, 20(%r11)
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
	stb %r8, 20(%r11)
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
	li %r11, 76
	stdbrx %r8, %r26, %r11
210:
	addi %r4, %r26, 20
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
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
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
