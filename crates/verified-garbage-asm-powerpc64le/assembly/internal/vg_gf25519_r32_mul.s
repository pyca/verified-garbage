// The functions of `src/internal/vg_gf25519_r32_mul.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r32_mul:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r12, %r3, %r4
	add %r10, %r3, %r5
	add %r6, %r3, %r6
	li %r0, 38
	li %r7, 0
	stw %r7, 864(%r3)
	stw %r7, 868(%r3)
	stw %r7, 872(%r3)
	stw %r7, 876(%r3)
	stw %r7, 880(%r3)
	stw %r7, 884(%r3)
	stw %r7, 888(%r3)
	stw %r7, 892(%r3)
	addi %r9, %r3, 0
	li %r11, 8
20:
	lwz %r4, 0(%r10)
	li %r8, 0
	lwz %r5, 0(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 4(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 8(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 12(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 16(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 20(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 24(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 28(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r10, %r10, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 864(%r3)
	lwz %r5, 896(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 0(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r3)
	lwz %r5, 900(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 4(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r3)
	lwz %r5, 904(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 8(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r3)
	lwz %r5, 908(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 12(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r3)
	lwz %r5, 912(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 16(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r3)
	lwz %r5, 916(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 20(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r3)
	lwz %r5, 920(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 24(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r3)
	lwz %r5, 924(%r3)
	mulld %r5, %r5, %r0
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 28(%r12)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r0
	lwz %r7, 0(%r12)
	add %r7, %r7, %r8
	stw %r7, 0(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r12)
	add %r7, %r7, %r8
	stw %r7, 4(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r12)
	add %r7, %r7, %r8
	stw %r7, 8(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r12)
	add %r7, %r7, %r8
	stw %r7, 12(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r12)
	add %r7, %r7, %r8
	stw %r7, 16(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r12)
	add %r7, %r7, %r8
	stw %r7, 20(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r12)
	add %r7, %r7, %r8
	stw %r7, 24(%r12)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r12)
	add %r7, %r7, %r8
	stw %r7, 28(%r12)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r0
	lwz %r7, 0(%r12)
	add %r7, %r7, %r8
	stw %r7, 0(%r12)
	blr
