// The functions of `src/internal/vg_sha1_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
