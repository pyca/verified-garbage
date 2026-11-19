// The functions of `src/internal/vg_poly1305_init_core.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init_core:
	ld %r5, 0(%r4)
	ld %r6, 8(%r4)
	ld %r7, 16(%r4)
	ld %r8, 24(%r4)
	std %r5, 24(%r3)
	std %r6, 32(%r3)
	std %r7, 40(%r3)
	std %r8, 48(%r3)
	li %r5, 0
	std %r5, 0(%r3)
	std %r5, 8(%r3)
	std %r5, 16(%r3)
	blr
