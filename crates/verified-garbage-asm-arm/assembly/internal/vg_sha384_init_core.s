// The functions of `src/internal/vg_sha384_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init_core:
	movw r12, #40664
	movt r12, #49413
	str r12, [r0, #0]
	movw r12, #40285
	movt r12, #52155
	str r12, [r0, #4]
	movw r12, #54535
	movt r12, #13948
	str r12, [r0, #8]
	movw r12, #10538
	movt r12, #25242
	str r12, [r0, #12]
	movw r12, #56599
	movt r12, #12400
	str r12, [r0, #16]
	movw r12, #346
	movt r12, #37209
	str r12, [r0, #20]
	movw r12, #22841
	movt r12, #63246
	str r12, [r0, #24]
	movw r12, #60632
	movt r12, #5423
	str r12, [r0, #28]
	movw r12, #2865
	movt r12, #65472
	str r12, [r0, #32]
	movw r12, #9831
	movt r12, #26419
	str r12, [r0, #36]
	movw r12, #5393
	movt r12, #26712
	str r12, [r0, #40]
	movw r12, #19079
	movt r12, #36532
	str r12, [r0, #44]
	movw r12, #36775
	movt r12, #25849
	str r12, [r0, #48]
	movw r12, #11789
	movt r12, #56076
	str r12, [r0, #52]
	movw r12, #20388
	movt r12, #48890
	str r12, [r0, #56]
	movw r12, #18461
	movt r12, #18357
	str r12, [r0, #60]
	bx lr
