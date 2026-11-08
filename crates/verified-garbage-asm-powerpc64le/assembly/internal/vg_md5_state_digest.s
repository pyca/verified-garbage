// The functions of `src/internal/vg_md5_state_digest.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_state_digest:
	addi %r9, %r26, 0
	addi %r10, %r28, 0
	addi %r26, %r3, 0
	addi %r28, %r4, 0
	lwz %r8, 0(%r26)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r26)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r26)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r26)
	stw %r8, 12(%r28)
	addi %r26, %r9, 0
	addi %r28, %r10, 0
	blr
	.p2align 6
