// The functions of `src/internal/vg_salsa20_8.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8:
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	lwz %r5, 0(%r3)
	lwz %r6, 4(%r3)
	lwz %r7, 8(%r3)
	lwz %r8, 12(%r3)
	lwz %r9, 16(%r3)
	lwz %r10, 20(%r3)
	lwz %r11, 24(%r3)
	lwz %r12, 28(%r3)
	lwz %r14, 32(%r3)
	lwz %r15, 36(%r3)
	lwz %r16, 40(%r3)
	lwz %r17, 44(%r3)
	lwz %r18, 48(%r3)
	lwz %r19, 52(%r3)
	lwz %r20, 56(%r3)
	lwz %r21, 60(%r3)
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	lwz %r0, 0(%r3)
	add %r5, %r5, %r0
	stw %r5, 0(%r3)
	lwz %r0, 4(%r3)
	add %r6, %r6, %r0
	stw %r6, 4(%r3)
	lwz %r0, 8(%r3)
	add %r7, %r7, %r0
	stw %r7, 8(%r3)
	lwz %r0, 12(%r3)
	add %r8, %r8, %r0
	stw %r8, 12(%r3)
	lwz %r0, 16(%r3)
	add %r9, %r9, %r0
	stw %r9, 16(%r3)
	lwz %r0, 20(%r3)
	add %r10, %r10, %r0
	stw %r10, 20(%r3)
	lwz %r0, 24(%r3)
	add %r11, %r11, %r0
	stw %r11, 24(%r3)
	lwz %r0, 28(%r3)
	add %r12, %r12, %r0
	stw %r12, 28(%r3)
	lwz %r0, 32(%r3)
	add %r14, %r14, %r0
	stw %r14, 32(%r3)
	lwz %r0, 36(%r3)
	add %r15, %r15, %r0
	stw %r15, 36(%r3)
	lwz %r0, 40(%r3)
	add %r16, %r16, %r0
	stw %r16, 40(%r3)
	lwz %r0, 44(%r3)
	add %r17, %r17, %r0
	stw %r17, 44(%r3)
	lwz %r0, 48(%r3)
	add %r18, %r18, %r0
	stw %r18, 48(%r3)
	lwz %r0, 52(%r3)
	add %r19, %r19, %r0
	stw %r19, 52(%r3)
	lwz %r0, 56(%r3)
	add %r20, %r20, %r0
	stw %r20, 56(%r3)
	lwz %r0, 60(%r3)
	add %r21, %r21, %r0
	stw %r21, 60(%r3)
	ld %r14, 0(%r4)
	ld %r15, 8(%r4)
	ld %r16, 16(%r4)
	ld %r17, 24(%r4)
	ld %r18, 32(%r4)
	ld %r19, 40(%r4)
	ld %r20, 48(%r4)
	ld %r21, 56(%r4)
	blr
