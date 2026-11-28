// The functions of `src/internal/vg_ed448_scalar_engine.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_engine:
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
20:
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
	bne %cr0, 20b
	blr
