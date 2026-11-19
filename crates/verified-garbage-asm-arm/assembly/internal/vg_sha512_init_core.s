// The functions of `src/internal/vg_sha512_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_init_core:
	movw r12, #51464
	movt r12, #62396
	str r12, [r0, #0]
	movw r12, #58983
	movt r12, #27145
	str r12, [r0, #4]
	movw r12, #42811
	movt r12, #33994
	str r12, [r0, #8]
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #12]
	movw r12, #63531
	movt r12, #65172
	str r12, [r0, #16]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #20]
	movw r12, #14065
	movt r12, #24349
	str r12, [r0, #24]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #28]
	movw r12, #33489
	movt r12, #44518
	str r12, [r0, #32]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #36]
	movw r12, #27679
	movt r12, #11070
	str r12, [r0, #40]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #44]
	movw r12, #48491
	movt r12, #64321
	str r12, [r0, #48]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #52]
	movw r12, #8569
	movt r12, #4990
	str r12, [r0, #56]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #60]
	bx lr
