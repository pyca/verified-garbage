// The functions of `src/internal/vg_sha256_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_init_core:
	movw r12, #58983
	movt r12, #27145
	str r12, [r0, #0]
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #4]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #8]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #12]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #16]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #20]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #24]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #28]
	bx lr
