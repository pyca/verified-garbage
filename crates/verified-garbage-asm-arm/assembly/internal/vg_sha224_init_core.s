// The functions of `src/internal/vg_sha224_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init_core:
	movw r12, #40664
	movt r12, #49413
	str r12, [r0, #0]
	movw r12, #54535
	movt r12, #13948
	str r12, [r0, #4]
	movw r12, #56599
	movt r12, #12400
	str r12, [r0, #8]
	movw r12, #22841
	movt r12, #63246
	str r12, [r0, #12]
	movw r12, #2865
	movt r12, #65472
	str r12, [r0, #16]
	movw r12, #5393
	movt r12, #26712
	str r12, [r0, #20]
	movw r12, #36775
	movt r12, #25849
	str r12, [r0, #24]
	movw r12, #20388
	movt r12, #48890
	str r12, [r0, #28]
	bx lr
