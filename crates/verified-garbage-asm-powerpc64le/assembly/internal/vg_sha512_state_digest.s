// The functions of `src/internal/vg_sha512_state_digest.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_state_digest:
	addi %r9, %r26, 0
	addi %r10, %r28, 0
	addi %r26, %r3, 0
	addi %r28, %r4, 0
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	ld %r8, 48(%r26)
	li %r11, 48
	stdbrx %r8, %r28, %r11
	ld %r8, 56(%r26)
	li %r11, 56
	stdbrx %r8, %r28, %r11
	addi %r26, %r9, 0
	addi %r28, %r10, 0
	blr
	.p2align 6
