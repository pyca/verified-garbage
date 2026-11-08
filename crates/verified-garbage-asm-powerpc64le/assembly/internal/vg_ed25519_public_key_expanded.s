// The functions of `src/internal/vg_ed25519_public_key_expanded.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key_expanded:
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
	ld %r8, 0(%r21)
	std %r8, 0(%r23)
	ld %r8, 8(%r21)
	std %r8, 8(%r23)
	ld %r8, 16(%r21)
	std %r8, 16(%r23)
	ld %r8, 24(%r21)
	std %r8, 24(%r23)
	ld %r8, 32(%r21)
	std %r8, 32(%r23)
	ld %r8, 40(%r21)
	std %r8, 40(%r23)
	ld %r8, 48(%r21)
	std %r8, 48(%r23)
	ld %r8, 56(%r21)
	std %r8, 56(%r23)
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
	.p2align 6
